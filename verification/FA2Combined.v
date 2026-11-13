From Coq Require Import List.
Require Import FullVM_WIP FA2LoopBody FA2DepositBody.
Import ListNotations.

(* The canonical complete FA2 transaction body, before ITER composition.
   Source translation checks equality to the parsed body. Callback meanings
   and interpreter/Octez correspondence remain external assumptions. *)
Definition canonical_iteration : list instruction :=
  FA2LoopBody.iteration_with FA2DepositBody.nonpositive_branch.
