(* SPDX-License-Identifier: MIT *)
From Coq Require Import List Arith.
Require Import InternalQueue ManagerBatch.
Import ListNotations.

(* Executable counterexamples for scheduler order, descendant failure,
   replay and rollback after an earlier asset effect. These are dispatcher
   model examples, not a substitute for the native protocol refinement. *)
Definition apply_example (ledger seen : list nat) (op : nat) :=
  if Nat.eqb op 9 then None else
  Some (ledger ++ [op], if Nat.eqb op 0 then [1] else []).

Example emitted_child_finishes_before_sibling :
  match run (fun n => n) apply_example 3 [] [] [0;2] with
  | Some result => executed result = [0;1;2] /\ final_context result = [0;1;2]
  | None => False end.
Proof. vm_compute. auto. Qed.

Example failure_rolls_back_prior_effect :
  atomic (fun n => n) apply_example 2 [42] [] [1;9] = (false,[42]).
Proof. reflexivity. Qed.

Example duplicate_nonce_rolls_back_prior_effect :
  atomic (fun n => n) apply_example 2 [42] [] [1;1] = (false,[42]).
Proof. reflexivity. Qed.

Definition failing_descendant (ledger seen : list nat) (op : nat) :=
  if Nat.eqb op 9 then None else
  Some (ledger ++ [op], if Nat.eqb op 0 then [9] else []).

Example descendant_failure_rolls_back_parent_and_skips_sibling :
  atomic (fun n => n) failing_descendant 3 [42] [] [0;2] = (false,[42]).
Proof. reflexivity. Qed.

(* The invalid alternative commits an earlier effect before a later error. *)
Definition broken_nonatomic_example : bool * list nat := (false,[42;1]).
Example non_atomic_variant_violates_rollback :
  snd broken_nonatomic_example <> [42].
Proof. discriminate. Qed.

Definition apply_root_example (ledger seen : list nat) (root : nat) :=
  Some (ledger ++ [100 + root], [root]).
Definition finish_example (ledger : list nat) :=
  if existsb (Nat.eqb 107) ledger then None else Some ledger.

Example batch_runs_root_children_before_next_root :
  atomic_batch (fun n => n) apply_example apply_root_example finish_example
    [0;2] 4 [42] [] = (true,[42;100;0;1;102;2]).
Proof. reflexivity. Qed.

Example failed_child_rolls_back_root_storage_and_prior_root :
  atomic_batch (fun n => n) apply_example apply_root_example finish_example
    [1;9;2] 3 [42] [] = (false,[42]).
Proof. reflexivity. Qed.

Example late_fee_failure_rolls_back_all_prior_storage_and_assets :
  atomic_batch (fun n => n) apply_example apply_root_example finish_example
    [1;7;2] 3 [42] [] = (false,[42]).
Proof. reflexivity. Qed.

Example internal_nonce_cannot_be_reused_by_next_root :
  atomic_batch (fun n => n) apply_example apply_root_example finish_example
    [1;1] 2 [42] [] = (false,[42]).
Proof. reflexivity. Qed.

(* The fee-collected snapshot is deliberately preserved on application
   failure. Tez fees are not refunded by the asset rollback theorem. *)
Example application_failure_keeps_upfront_fee_snapshot :
  atomic_batch (fun n => n) apply_example apply_root_example finish_example
    [9] 1 [88;42] [] = (false,[88;42]).
Proof. reflexivity. Qed.
