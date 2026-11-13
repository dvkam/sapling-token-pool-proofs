(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String Arith Lia.
Require Import MichelineRaw MichelinePrograms.
Import ListNotations.
Open Scope list_scope.

Fixpoint encode (n : node) : list token :=
  let fix encode_children (xs : list node) :=
    match xs with [] => [] | x :: rest => encode x ++ encode_children rest end in
  match n with
  | MInt s => [TInt s] | MString s => [TString s] | MBytes s => [TBytes s]
  | MPrim name args ann => TPrim name (List.length args) ann :: encode_children args
  | MSeq xs => TSeq (List.length xs) :: encode_children xs
  end.

Definition encode_forest (xs : list node) : list token :=
  (fix encode_children (ys : list node) :=
    match ys with [] => [] | y :: rest => encode y ++ encode_children rest end) xs.
Definition parse_children (parse : list token -> option (node * list token)) :=
  fix children (n : nat) (xs : list token) : option (list node * list token) :=
  match n with
  | O => Some ([], xs)
  | S n' => match parse xs with
    | None => None
    | Some (v, tail) => match children n' tail with
      | None => None | Some (vs, final) => Some (v :: vs, final) end
    end
  end.

Lemma parse_children_encode : forall parse xs,
  (forall x, In x xs -> forall tail, parse (encode x ++ tail) = Some (x,tail)) ->
  forall tail, parse_children parse (List.length xs) (encode_forest xs ++ tail) = Some (xs,tail).
Proof.
  intros parse xs. induction xs as [|x xs IH]; intros H tail; cbn [List.length parse_children encode_forest flat_map].
  - reflexivity.
  - rewrite <- app_assoc. rewrite H by (left; reflexivity).
    rewrite IH; [reflexivity|]. intros; apply H; right; assumption.
Qed.

Lemma encoded_child_length : forall xs x,
  In x xs -> List.length (encode x) <= List.length (encode_forest xs).
Proof.
  intros xs; induction xs as [|a xs IH]; intros x H; [contradiction|].
  cbn [encode_forest flat_map]. rewrite app_length. destruct H as [E|H].
  - subst. lia.
  - specialize (IH x H). unfold encode_forest in IH. lia.
Qed.

Theorem decode_encode_with_fuel : forall fuel n tail,
  List.length (encode n) < fuel -> decode fuel (encode n ++ tail) = Some (n,tail).
Proof.
  induction fuel as [|fuel IH]; intros n tail Hlen; [lia|].
  destruct n as [s|s|s|name args ann|items].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [encode decode app]. fold encode_forest. fold (parse_children (decode fuel)).
    rewrite parse_children_encode; [reflexivity|].
    intros x Hin rest. apply IH. pose proof (encoded_child_length args x Hin).
    change (S (List.length (encode_forest args)) < S fuel) in Hlen. lia.
  - cbn [encode decode app]. fold encode_forest. fold (parse_children (decode fuel)).
    rewrite parse_children_encode; [reflexivity|].
    intros x Hin rest. apply IH. pose proof (encoded_child_length items x Hin).
    change (S (List.length (encode_forest items)) < S fuel) in Hlen. lia.
Qed.

Corollary decode_encode_complete : forall n,
  decode_complete (S (List.length (encode n))) (encode n) = Some n.
Proof.
  intros n. unfold decode_complete.
  pose proof (decode_encode_with_fuel (S (List.length (encode n))) n [] ltac:(lia)) as H.
  rewrite app_nil_r in H. rewrite H. reflexivity.
Qed.
Print Assumptions decode_encode_complete.

Corollary encode_injective : forall a b, encode a = encode b -> a = b.
Proof.
  intros a b H.
  pose proof (decode_encode_complete a) as A.
  pose proof (decode_encode_complete b) as B.
  rewrite H in A.
  rewrite A in B. now inversion B.
Qed.
Print Assumptions encode_injective.

(* Coq itself independently serializes each generated raw tree, rather than
   trusting the generator to align its own token and tree representations.
   JSON-to-Coq source import is still a trusted step. *)
Example fa12_tokens_match_independent_encoder : encode fa12_expected = fa12_tokens.
Proof. vm_compute. reflexivity. Qed.
Example fa2_tokens_match_independent_encoder : encode fa2_expected = fa2_tokens.
Proof. vm_compute. reflexivity. Qed.
Example ticket_tokens_match_independent_encoder : encode ticket_expected = ticket_tokens.
Proof. vm_compute. reflexivity. Qed.
Example ingress_tokens_match_independent_encoder : encode ingress_expected = ingress_tokens.
Proof. vm_compute. reflexivity. Qed.
Example egress_tokens_match_independent_encoder : encode egress_expected = egress_tokens.
Proof. vm_compute. reflexivity. Qed.
