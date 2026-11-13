From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP FA12LoopBody.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* Inversion of the actual source-shaped address guard in the partial VM.
   Complete UNPACK/PACK equations are premises. This does not establish the
   relation of those equations, or the encoding length, to Octez. *)
Section AddressGuard.
  Variable primitive : string -> stack -> option stack.
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Hypothesis unpack_some_frame : forall bound recipient rest,
    unpack bound = Some recipient ->
    primitive "UNPACK_address" (bound :: rest) = Some (VSome recipient :: rest).
  Hypothesis unpack_none_frame : forall bound rest,
    unpack bound = None ->
    primitive "UNPACK_address" (bound :: rest) = Some (VNone :: rest).
  Hypothesis pack_frame : forall recipient rest,
    primitive "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).

  Lemma guard_none_rejects : forall fuel bound rest,
    unpack bound = None ->
    run primitive (15 + fuel)%nat address_guard (bound :: rest) = None.
  Proof.
    intros fuel bound rest H.
    change (run primitive (S (14 + fuel)) address_guard (bound :: rest) = None).
    rewrite address_unpack_step, (unpack_none_frame bound rest H).
    change (run primitive (4 + (10 + fuel))%nat address_unpacked (VNone :: rest) = None).
    apply address_none_bad.
  Qed.

  Lemma guard_some_reduces : forall fuel bound recipient rest,
    unpack bound = Some recipient ->
    run primitive (15 + fuel)%nat address_guard (bound :: rest) =
      if Nat.eqb 28 (List.length (pack recipient))
      then Some (recipient :: rest) else None.
  Proof.
    intros fuel bound recipient rest H.
    change (15 + fuel)%nat with (S (14 + fuel))%nat.
    rewrite address_unpack_step, (unpack_some_frame bound recipient rest H).
    change (14 + fuel)%nat with (3 + (11 + fuel))%nat.
    rewrite address_pack_step, pack_frame.
    change (11 + fuel)%nat with (4 + (7 + fuel))%nat.
    rewrite address_compare_step.
    destruct (Nat.compare 28 (List.length (pack recipient))) eqn:E.
    - apply Nat.compare_eq_iff in E. rewrite <- E, Nat.eqb_refl.
      apply address_if_good.
    - assert (B : Nat.eqb 28 (List.length (pack recipient)) = false).
      { apply Nat.eqb_neq. intro EQ. rewrite EQ, Nat.compare_refl in E. discriminate. }
      rewrite B. apply address_if_bad.
    - assert (B : Nat.eqb 28 (List.length (pack recipient)) = false).
      { apply Nat.eqb_neq. intro EQ. rewrite EQ, Nat.compare_refl in E. discriminate. }
      rewrite B. apply address_if_bad.
  Qed.

  Theorem guard_success_inverse : forall fuel bound rest output,
    run primitive (15 + fuel)%nat address_guard (bound :: rest) = Some output ->
    exists recipient, unpack bound = Some recipient /\
      List.length (pack recipient) = 28%nat /\ output = recipient :: rest.
  Proof.
    intros fuel bound rest output H.
    destruct (unpack bound) as [recipient|] eqn:U.
    - rewrite (guard_some_reduces fuel bound recipient rest U) in H.
      destruct (Nat.eqb 28 (List.length (pack recipient))) eqn:B; try discriminate.
      apply Nat.eqb_eq in B. inversion H; subst.
      exists recipient. repeat split; auto.
    - rewrite (guard_none_rejects fuel bound rest U) in H. discriminate.
  Qed.

  Corollary guard_bad_length_rejects : forall fuel bound recipient rest,
    unpack bound = Some recipient ->
    List.length (pack recipient) <> 28%nat ->
    run primitive (15 + fuel)%nat address_guard (bound :: rest) = None.
  Proof.
    intros fuel bound recipient rest H LEN.
    rewrite (guard_some_reduces fuel bound recipient rest H).
    destruct (Nat.eqb 28 (List.length (pack recipient))) eqn:E; auto.
    apply Nat.eqb_eq in E. exfalso. auto.
  Qed.
End AddressGuard.
Print Assumptions guard_success_inverse.
