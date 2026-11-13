From Coq Require Import List String.
Require Import FullVM_WIP FA2Operations.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Section Groups.
  Variable prim : string -> stack -> option stack.
  Variable pool : value.
  Hypothesis self_frame : forall s, prim "SELF_ADDRESS" s = Some (pool :: s).

  Lemma deposit_group_step_fuel : forall fuel payer amount groups handle state withdrawals token token_id frame,
    run prim (12 + fuel)%nat deposit_group_body
      (VPair payer amount :: VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    Some (VList (deposit_group pool token_id payer amount :: groups) ::
      handle :: state :: withdrawals :: token :: token_id :: frame).
  Proof. intros; rewrite (deposit_prefix prim (8 + fuel)%nat), self_frame; reflexivity. Qed.

  Lemma deposit_iterate_fuel : forall fuel entries groups handle state withdrawals token token_id frame,
    iterate (fun x s => run prim (12 + fuel)%nat deposit_group_body (x :: s))
      (List.map (fun entry => VPair (fst entry) (snd entry)) entries)
      (VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    Some (VList (reverse_deposit_groups pool entries groups token_id) ::
      handle :: state :: withdrawals :: token :: token_id :: frame).
  Proof.
    intros fuel entries; induction entries as [|[payer amount] entries IH]; intros; cbn [List.map iterate reverse_deposit_groups].
    - reflexivity.
    - rewrite deposit_group_step_fuel. apply IH.
  Qed.

  Theorem unbounded_deposit_group_iteration_fuel : forall fuel entries groups handle state withdrawals token token_id frame,
    run prim (13 + fuel)%nat [Iter deposit_group_body]
      (VMap entries :: VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame) =
    Some (VList (reverse_deposit_groups pool entries groups token_id) ::
      handle :: state :: withdrawals :: token :: token_id :: frame).
  Proof.
    intros; rewrite (map_iter_step prim (11 + fuel)%nat).
    change (match iterate (fun x s => run prim (12 + fuel)%nat deposit_group_body (x :: s))
      (List.map (fun entry => VPair (fst entry) (snd entry)) entries)
      (VList groups :: handle :: state :: withdrawals :: token :: token_id :: frame)
      with Some out => Some out | None => None end =
    Some (VList (reverse_deposit_groups pool entries groups token_id) ::
      handle :: state :: withdrawals :: token :: token_id :: frame)).
    rewrite deposit_iterate_fuel. reflexivity.
  Qed.
End Groups.
Print Assumptions unbounded_deposit_group_iteration_fuel.
