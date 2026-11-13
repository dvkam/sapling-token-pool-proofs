(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith Lia.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope Z_scope.

(* The checker binds this program to the parsed source. This executes the real source-shaped final
   credit check and output construction in the partial VM, not Octez. *)
Definition final_code : list instruction :=
  [Dig 2; ToInt; IsEq; If [] [Unit; Fail]; PairN 3; Swap; Nil; Swap;
   Iter [Cons]; Pair].

Section Output.
  Variable primitive : String.string -> stack -> option stack.

  Lemma cons_fuel : forall fuel x xs frame,
    run primitive (2 + fuel)%nat [Cons] (x :: VList xs :: frame) =
    Some (VList (x :: xs) :: frame).
  Proof. reflexivity. Qed.

  Lemma iterate_cons_fuel : forall fuel xs acc frame,
    iterate (fun x s => run primitive (2 + fuel)%nat [Cons] (x :: s))
      xs (VList acc :: frame) =
    Some (VList (rev xs ++ acc) :: frame).
  Proof.
    intros fuel xs. induction xs as [|x xs IH]; intros acc frame; cbn [iterate].
    - reflexivity.
    - rewrite cons_fuel, IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma zero_credit_prefix : forall fuel state held asset ops frame,
    run primitive (9 + S fuel)%nat final_code
      (state :: held :: VNat 0 :: asset :: VList ops :: frame) =
    run primitive (S (S fuel)) [Iter [Cons]; Pair]
      (VList ops :: VList [] :: VPair state (VPair held asset) :: frame).
  Proof. reflexivity. Qed.

  Lemma reverse_output_step : forall fuel ops acc storage frame,
    run primitive (S (S fuel)) [Iter [Cons]; Pair]
      (VList ops :: VList acc :: storage :: frame) =
    match iterate (fun x s => run primitive (S fuel) [Cons] (x :: s))
      ops (VList acc :: storage :: frame) with
    | Some s => run primitive (S fuel) [Pair] s | None => None end.
  Proof. reflexivity. Qed.

  Lemma pair_output_step : forall fuel xs storage frame,
    run primitive (2 + fuel)%nat [Pair] (VList xs :: storage :: frame) =
    Some (VPair (VList xs) storage :: frame).
  Proof. reflexivity. Qed.

  Lemma credit_check_step : forall fuel credit state held asset ops frame,
    run primitive (3 + fuel)%nat final_code
      (state :: held :: VNat credit :: asset :: VList ops :: frame) =
    run primitive fuel (skipn 3 final_code)
      (VBool (Z.eqb (Z.of_nat credit) 0) :: state :: held :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma false_credit_check : forall fuel state held asset ops frame,
    run primitive (4 + fuel)%nat (skipn 3 final_code)
      (VBool false :: state :: held :: asset :: VList ops :: frame) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.

  Theorem zero_credit_returns_ordered_operations_and_storage :
    forall state held asset ops frame,
    run primitive 40 final_code
      (state :: held :: VNat 0 :: asset :: VList ops :: frame) =
    Some (VPair (VList (rev ops)) (VPair state (VPair held asset)) :: frame).
  Proof.
    intros. rewrite (zero_credit_prefix 30), (reverse_output_step 30).
    rewrite (iterate_cons_fuel 29), app_nil_r.
    apply (pair_output_step 29).
  Qed.

  Theorem zero_credit_returns_at_fuel : forall fuel state held asset ops frame,
    run primitive (40 + fuel)%nat final_code
      (state :: held :: VNat 0 :: asset :: VList ops :: frame) =
    Some (VPair (VList (rev ops)) (VPair state (VPair held asset)) :: frame).
  Proof.
    intros. rewrite (zero_credit_prefix (30 + fuel)%nat), (reverse_output_step (30 + fuel)%nat).
    rewrite (iterate_cons_fuel (29 + fuel)%nat), app_nil_r.
    apply (pair_output_step (29 + fuel)%nat).
  Qed.

  Theorem unmatched_received_credit_rejects :
    forall credit state held asset ops frame,
    (0 < credit)%nat ->
    run primitive 40 final_code
      (state :: held :: VNat credit :: asset :: VList ops :: frame) = None.
  Proof.
    intros credit state held asset ops frame H.
    assert (E : Z.eqb (Z.of_nat credit) 0 = false)
      by (apply Z.eqb_neq; lia).
    rewrite (credit_check_step 37), E. apply (false_credit_check 33).
  Qed.
End Output.

Print Assumptions zero_credit_returns_ordered_operations_and_storage.
Print Assumptions zero_credit_returns_at_fuel.
Print Assumptions unmatched_received_credit_rejects.
