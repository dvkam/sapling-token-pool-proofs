From Coq Require Import List String.
Require Import FullVM_WIP.
Import ListNotations.

(* Generic composition theorem. The per-input body equation is a hypothesis,
   not a proved FA2 refinement. It permits arbitrary state and input lists and
   does not assume the conclusion about the whole loop. *)
Section LoopInduction.
  Variable primitive : string -> stack -> option stack.
  Variable body : list instruction.
  Variable step : value -> stack -> option stack.
  Variable fuel : nat.
  Hypothesis body_refines : forall x s,
    run primitive (S fuel) body (x :: s) = step x s.

  Lemma iterate_refines : forall xs s,
    iterate (fun x st => run primitive (S fuel) body (x :: st)) xs s =
      iterate step xs s.
  Proof.
    induction xs as [|x xs IH]; intros s; cbn [iterate fold_left].
    - reflexivity.
    - rewrite body_refines. destruct (step x s); [apply IH | reflexivity].
  Qed.

  Theorem source_loop_unbounded : forall xs s,
    run primitive (S (S fuel)) [Iter body] (VList xs :: s) =
      iterate step xs s.
  Proof.
    intros xs s. cbn [run]. rewrite iterate_refines.
    destruct (iterate step xs s); reflexivity.
  Qed.
End LoopInduction.
