From Coq Require Import List String ZArith.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* Successful source ITER body over the deposit map. This only constructs
   groups; it does not prove CONTRACT, TRANSFER_TOKENS, map ordering, or
   token execution. *)
Definition deposit_group_body : list instruction :=
  [Unpair; Swap; Dup 8; Prim "SELF_ADDRESS"; PairN 3; Nil; Swap; Cons; Swap; Pair; Cons].
Definition deposit_group_tail : list instruction :=
  [PairN 3; Nil; Swap; Cons; Swap; Pair; Cons].
Definition deposit_group (pool token_id payer amount : value) : value :=
  VPair payer (VList [VPair pool (VPair token_id amount)]).

Definition withdrawal_item_body : list instruction :=
  [Unpair; Dup 7; Swap; PairN 3].

(* Actual MAP body: preserve the recipient/amount and insert the stored token
   id. This single-step fact does not prove the surrounding MAP or transfer. *)
Lemma withdrawal_item_exact : forall prim recipient amount groups handle state token token_id frame,
  run prim 8 withdrawal_item_body
    (VPair recipient amount :: groups :: handle :: state :: token :: token_id :: frame) =
  Some (VPair recipient (VPair token_id amount) :: groups :: handle :: state :: token :: token_id :: frame).
Proof. reflexivity. Qed.

Section Groups.
  Variable prim : string -> stack -> option stack.
  Variable pool : value.
  Hypothesis self_frame : forall s, prim "SELF_ADDRESS" s = Some (pool :: s).

  Lemma deposit_prefix : forall fuel payer amount groups handle state withdrawals token token_id frame,
    run prim (4 + fuel)%nat deposit_group_body
      (VPair payer amount :: VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    match prim "SELF_ADDRESS"
      (token_id :: amount :: payer :: VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) with
    | Some s => run prim fuel deposit_group_tail s | None => None end.
  Proof. reflexivity. Qed.

  Lemma deposit_group_step : forall payer amount groups handle state withdrawals token token_id frame,
    run prim 20 deposit_group_body
      (VPair payer amount :: VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    Some (VList (deposit_group pool token_id payer amount :: groups) ::
      handle :: state :: withdrawals :: token :: token_id :: frame).
  Proof. intros; rewrite (deposit_prefix 16), self_frame; reflexivity. Qed.

  Fixpoint reverse_deposit_groups (entries : list (value * value)) (groups : list value) (token_id : value) : list value :=
    match entries with
    | [] => groups
    | (payer, amount) :: rest => reverse_deposit_groups rest (deposit_group pool token_id payer amount :: groups) token_id
    end.

  Lemma deposit_groups_reverse_entries : forall entries groups token_id,
    reverse_deposit_groups entries groups token_id =
    List.rev (List.map (fun entry => deposit_group pool token_id (fst entry) (snd entry)) entries) ++ groups.
  Proof.
    induction entries as [|[payer amount] entries IH]; intros groups token_id.
    - reflexivity.
    - cbn [reverse_deposit_groups List.map List.rev].
      rewrite IH, <- app_assoc. reflexivity.
  Qed.

  Lemma deposit_iterate : forall entries groups handle state withdrawals token token_id frame,
    iterate (fun x s => run prim 20 deposit_group_body (x :: s))
      (List.map (fun entry => VPair (fst entry) (snd entry)) entries)
      (VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    Some (VList (reverse_deposit_groups entries groups token_id) ::
      handle :: state :: withdrawals :: token :: token_id :: frame).
  Proof.
    induction entries as [|[payer amount] entries IH]; intros; cbn [List.map iterate reverse_deposit_groups].
    - reflexivity.
    - rewrite deposit_group_step. apply IH.
  Qed.

  Lemma map_iter_step : forall fuel entries s,
    run prim (S (S fuel)) [Iter deposit_group_body] (VMap entries :: s) =
    match iterate (fun x st => run prim (S fuel) deposit_group_body (x :: st))
      (List.map (fun entry => VPair (fst entry) (snd entry)) entries) s with
    | Some result => Some result | None => None end.
  Proof. reflexivity. Qed.

  Theorem unbounded_deposit_group_iteration : forall entries groups handle state withdrawals token token_id frame,
    run prim 21 [Iter deposit_group_body]
      (VMap entries :: VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    Some (VList (reverse_deposit_groups entries groups token_id) ::
      handle :: state :: withdrawals :: token :: token_id :: frame).
  Proof.
    intros; rewrite (map_iter_step 19), deposit_iterate. reflexivity.
  Qed.
End Groups.
Print Assumptions withdrawal_item_exact.
Print Assumptions unbounded_deposit_group_iteration.
