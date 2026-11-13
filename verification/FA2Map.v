From Coq Require Import List String.
Require Import FullVM_WIP FA2Operations.
Import ListNotations.
Open Scope list_scope.

Fixpoint map_items (prim : string -> stack -> option stack) (fuel : nat)
  (xs : list value) (acc : stack) : option (list value * stack) :=
  match xs with
  | [] => Some ([], acc)
  | x :: xs' =>
      match run prim fuel withdrawal_item_body (x :: acc) with
      | Some (y :: next) =>
          match map_items prim fuel xs' next with
          | Some (ys, final) => Some (y :: ys, final)
          | None => None end
      | _ => None end
  end.


Definition local_items (prim : string -> stack -> option stack) (fuel : nat) :=
  fix go (xs : list value) (acc : stack) : option (list value * stack) :=
  match xs with
  | [] => Some ([], acc)
  | x :: xs' =>
      match run prim fuel withdrawal_item_body (x :: acc) with
      | Some (y :: next) =>
          match go xs' next with
          | Some (ys, final) => Some (y :: ys, final)
          | None => None end
      | _ => None end
  end.

Lemma local_items_match : forall prim fuel xs acc,
  local_items prim fuel xs acc = map_items prim fuel xs acc.
Proof.
  intros prim fuel xs; induction xs as [|x xs IH]; intros acc.
  - reflexivity.
  - cbn [local_items map_items].
    destruct (run prim fuel withdrawal_item_body (x :: acc)) as [[|y next]|]; try reflexivity.
    rewrite IH. reflexivity.
Qed.

Lemma map_outer : forall prim fuel xs acc,
  run prim (S (S fuel)) [Map withdrawal_item_body] (VList xs :: acc) =
  match local_items prim (S fuel) xs acc with
  | Some (ys, final) => Some (VList ys :: final) | None => None end.
Proof.
  intros prim fuel xs acc.
  change ((match (match local_items prim (S fuel) xs acc with
    | Some (ys, final) => Some (VList ys :: final) | None => None end) with
    | Some s => Some s | None => None end) =
    match local_items prim (S fuel) xs acc with
    | Some (ys, final) => Some (VList ys :: final) | None => None end).
  destruct (local_items prim (S fuel) xs acc) as [[ys final]|]; reflexivity.
Qed.

Lemma map_step : forall prim fuel xs acc,
  run prim (S (S fuel)) [Map withdrawal_item_body] (VList xs :: acc) =
  match map_items prim (S fuel) xs acc with
  | Some (ys, final) => Some (VList ys :: final) | None => None end.
Proof. intros; rewrite map_outer, local_items_match; reflexivity. Qed.

Lemma withdrawal_item_fuel9 : forall prim recipient amount groups handle state token token_id frame,
  run prim 9 withdrawal_item_body
    (VPair recipient amount :: groups :: handle :: state :: token :: token_id :: frame) =
  Some (VPair recipient (VPair token_id amount) :: groups :: handle :: state :: token :: token_id :: frame).
Proof. reflexivity. Qed.

Lemma mapped_items_exact : forall prim entries groups handle state token token_id frame,
  map_items prim 9
    (List.map (fun entry => VPair (fst entry) (snd entry)) entries)
    (groups :: handle :: state :: token :: token_id :: frame) =
  Some (List.map (fun entry => VPair (fst entry) (VPair token_id (snd entry))) entries,
        groups :: handle :: state :: token :: token_id :: frame).
Proof.
  intros prim entries; induction entries as [|[recipient amount] entries IH];
    intros groups handle state token token_id frame; cbn [List.map map_items].
  - reflexivity.
  - rewrite withdrawal_item_fuel9, IH. reflexivity.
Qed.

Theorem unbounded_withdrawal_mapping :
  forall prim entries groups handle state token token_id frame,
  run prim 10 [Map withdrawal_item_body]
    (VList (List.map (fun entry => VPair (fst entry) (snd entry)) entries) ::
     groups :: handle :: state :: token :: token_id :: frame) =
  Some (VList (List.map (fun entry => VPair (fst entry) (VPair token_id (snd entry))) entries) ::
        groups :: handle :: state :: token :: token_id :: frame).
Proof. intros; rewrite (map_step prim 8), mapped_items_exact; reflexivity. Qed.
Print Assumptions unbounded_withdrawal_mapping.
