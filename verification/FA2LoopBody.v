From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Local Opaque Nat.compare.

(* One actual control-flow path of the FA2 ITER body, in the partial VM.
   This is not an Octez correspondence theorem or a whole-loop invariant.
   verify abstracts SAPLING_VERIFY_UPDATE, unpack abstracts UNPACK address,
   and pack supplies canonical PACK address bytes. Their real meanings and
   the source-to-VM mapping remain external obligations. Nonpositive balances
   are deliberately outside this module; their branch is a parameter.
   Error payloads/gas/rollback are not represented by this VM. *)
Section PositiveFA2Path.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable primitive : string -> stack -> option stack.
  (* These local frame equations are explicit theorem premises, not axioms
     about Octez. A common concrete environment must separately satisfy them. *)
  Hypothesis unpack_some_frame : forall bound recipient rest,
    unpack bound = Some recipient ->
    primitive "UNPACK_address" (bound :: rest) = Some (VSome recipient :: rest).
  Hypothesis unpack_none_frame : forall bound rest,
    unpack bound = None ->
    primitive "UNPACK_address" (bound :: rest) = Some (VNone :: rest).
  Hypothesis pack_frame : forall recipient rest,
    primitive "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).
  Hypothesis verify_some_frame : forall tx old bound balance next rest,
    verify tx old = Some (bound, balance, next) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis verify_none_frame : forall tx old rest,
    verify tx old = None ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) = Some (VNone :: rest).

  (* The positive IF branch, including the entire recipient guard and exact
     CONS/DUG stack rearrangement. The error literal is represented by its
     UTF-8 bytes and immediately consumed by FAILWITH. *)
  Definition accumulate_tail : list instruction :=
    [If [] [Push (VString ([70;65;95;78;79;78;95;68;69;70;65;85;76;84;95;82;69;67;73;80;73;69;78;84]%nat)); Fail];
     Pair; Dig 3; Swap; Cons; Dug 2].
  Definition packed_tail : list instruction :=
    [Size; Push (VNat 28); CompareInt; IsEq] ++ accumulate_tail.
  Definition unpacked_tail : list instruction :=
    [IfNone [Unit; Fail] []; Dup 1; Prim "PACK_address"] ++ packed_tail.
  Definition withdrawal_branch : list instruction :=
    [Drop; Dig 2; Prim "UNPACK_address"] ++ unpacked_tail.

  (* The true path is independent of the not-taken false branch. This lets a
     caller instantiate the exact nonpositive source program using the same
     primitive environment, rather than assume a projection is equivalent. *)
  Definition iteration_with (negative : list instruction) : list instruction :=
    [Prim "SAPLING_VERIFY_UPDATE"; IfNone [Unit; Fail] []; UnpairN 3;
     Dug 2; Dup 1; Dup 1; Abs; Dug 2; IsGt;
     If withdrawal_branch negative].
  Definition positive_iteration : list instruction :=
    iteration_with [Prim "NONPOSITIVE_BRANCH_NOT_MODELED"].

  Lemma unpack_prefix_step : forall fuel balance amount state bound deposits ws frame,
    run primitive (3 + fuel)%nat withdrawal_branch
      (VInt balance :: VNat amount :: state :: bound :: deposits :: VList ws :: frame) =
    match primitive "UNPACK_address" (bound :: VNat amount :: state :: deposits :: VList ws :: frame) with
    | Some s => run primitive fuel unpacked_tail s | None => None end.
  Proof. reflexivity. Qed.
  Lemma pack_prefix_step : forall fuel recipient amount state deposits ws frame,
    run primitive (3 + fuel)%nat unpacked_tail
      (VSome recipient :: VNat amount :: state :: deposits :: VList ws :: frame) =
    match primitive "PACK_address" (recipient :: recipient :: VNat amount :: state :: deposits :: VList ws :: frame) with
    | Some s => run primitive fuel packed_tail s | None => None end.
  Proof. reflexivity. Qed.
  Lemma guard_prefix_step : forall fuel bytes recipient amount state deposits ws frame,
    run primitive (4 + fuel)%nat packed_tail
      (VBytes bytes :: recipient :: VNat amount :: state :: deposits :: VList ws :: frame) =
    run primitive fuel accumulate_tail
      (VBool (Z.eqb (match Nat.compare 28 (List.length bytes) with Lt => -1 | Eq => 0 | Gt => 1 end) 0) ::
       recipient :: VNat amount :: state :: deposits :: VList ws :: frame).
  Proof. reflexivity. Qed.
  Lemma accumulate_step : forall fuel recipient amount state deposits ws frame,
    run primitive (7 + fuel)%nat accumulate_tail
      (VBool true :: recipient :: VNat amount :: state :: deposits :: VList ws :: frame) =
    Some (state :: deposits :: VList (VPair recipient (VNat amount) :: ws) :: frame).
  Proof. reflexivity. Qed.
  Lemma accumulate_failure_step : forall fuel recipient amount state deposits ws frame,
    run primitive (4 + fuel)%nat accumulate_tail
      (VBool false :: recipient :: VNat amount :: state :: deposits :: VList ws :: frame) = None.
  Proof. reflexivity. Qed.
  Lemma verify_prefix_step : forall negative fuel tx old deposits ws frame,
    run primitive (S fuel) (iteration_with negative) (tx :: old :: deposits :: VList ws :: frame) =
    match primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: deposits :: VList ws :: frame) with
    | Some s => run primitive fuel (tl (iteration_with negative)) s | None => None end.
  Proof. reflexivity. Qed.
  Lemma verified_numeric_prefix_step : forall negative fuel bound balance state deposits ws frame,
    run primitive (9 + S fuel)%nat (tl (iteration_with negative))
      (VSome (VPair bound (VPair (VInt balance) state)) :: deposits :: VList ws :: frame) =
    match run primitive (S fuel)
      (if Z.gtb balance 0 then withdrawal_branch else negative)
      (VInt balance :: VNat (Z.to_nat (Z.abs balance)) :: state :: bound :: deposits :: VList ws :: frame) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Lemma unpack_failure_step : forall fuel amount state deposits ws frame,
    run primitive (4 + fuel)%nat unpacked_tail
      (VNone :: VNat amount :: state :: deposits :: VList ws :: frame) = None.
  Proof. reflexivity. Qed.
  Lemma verify_failure_step : forall negative fuel deposits ws frame,
    run primitive (4 + fuel)%nat (tl (iteration_with negative))
      (VNone :: deposits :: VList ws :: frame) = None.
  Proof. reflexivity. Qed.
  Local Opaque run.

  Theorem withdrawal_branch_updates_exact_stack_fuel :
    forall padding balance amount bound_data recipient new_state deposits withdrawals frame,
    unpack bound_data = Some recipient -> List.length (pack recipient) = 28%nat ->
    run primitive (17 + padding)%nat withdrawal_branch
      (VInt balance :: VNat amount :: new_state :: bound_data :: deposits :: VList withdrawals :: frame) =
    Some (new_state :: deposits :: VList (VPair recipient (VNat amount) :: withdrawals) :: frame).
  Proof.
    intros padding balance amount bound_data recipient new_state deposits withdrawals frame HU HP.
    rewrite (unpack_prefix_step (14 + padding)%nat).
    rewrite (unpack_some_frame bound_data recipient) by exact HU.
    rewrite (pack_prefix_step (11 + padding)%nat), pack_frame.
    rewrite (guard_prefix_step (7 + padding)%nat), HP, Nat.compare_refl.
    apply (accumulate_step padding).
  Qed.

  Theorem withdrawal_branch_rejects_noncanonical_length_fuel :
    forall padding balance amount bound_data recipient new_state deposits withdrawals frame,
    unpack bound_data = Some recipient -> List.length (pack recipient) <> 28%nat ->
    run primitive (17 + padding)%nat withdrawal_branch
      (VInt balance :: VNat amount :: new_state :: bound_data :: deposits :: VList withdrawals :: frame) = None.
  Proof.
    intros padding balance amount bound_data recipient new_state deposits withdrawals frame HU HP.
    rewrite (unpack_prefix_step (14 + padding)%nat).
    rewrite (unpack_some_frame bound_data recipient) by exact HU.
    rewrite (pack_prefix_step (11 + padding)%nat), pack_frame, (guard_prefix_step (7 + padding)%nat).
    destruct (Nat.compare 28 (List.length (pack recipient))) eqn:HC.
    - exfalso. apply HP. symmetry. now apply Nat.compare_eq_iff.
    - apply (accumulate_failure_step (3 + padding)%nat).
    - apply (accumulate_failure_step (3 + padding)%nat).
  Qed.

  Theorem withdrawal_branch_updates_exact_stack :
    forall balance amount bound_data recipient new_state deposits withdrawals frame,
    unpack bound_data = Some recipient ->
    List.length (pack recipient) = 28%nat ->
    run primitive 80 withdrawal_branch
      (VInt balance :: VNat amount :: new_state :: bound_data :: deposits ::
       VList withdrawals :: frame) =
    Some (new_state :: deposits ::
          VList (VPair recipient (VNat amount) :: withdrawals) :: frame).
  Proof.
    intros balance amount bound_data recipient new_state deposits withdrawals frame HU HP.
    rewrite (unpack_prefix_step 77).
    rewrite (unpack_some_frame bound_data recipient) by exact HU.
    rewrite (pack_prefix_step 74).
    rewrite pack_frame.
    rewrite (guard_prefix_step 70), HP, Nat.compare_refl.
    apply (accumulate_step 63).
  Qed.

  Theorem withdrawal_branch_rejects_bad_unpack :
    forall balance amount bound_data new_state deposits withdrawals frame,
    unpack bound_data = None ->
    run primitive 80 withdrawal_branch
      (VInt balance :: VNat amount :: new_state :: bound_data :: deposits ::
       VList withdrawals :: frame) = None.
  Proof.
    intros balance amount bound_data new_state deposits withdrawals frame HU.
    rewrite (unpack_prefix_step 77), unpack_none_frame by exact HU.
    apply (unpack_failure_step 73).
  Qed.

  Theorem verified_positive_iteration_with_updates_exact_stack :
    forall negative tx old_state bound_data balance new_state recipient deposits withdrawals frame,
    verify tx old_state = Some (bound_data, balance, new_state) ->
    0 < balance ->
    unpack bound_data = Some recipient ->
    List.length (pack recipient) = 28%nat ->
    run primitive 90 (iteration_with negative)
      (tx :: old_state :: deposits :: VList withdrawals :: frame) =
    Some (new_state :: deposits ::
          VList (VPair recipient (VNat (Z.to_nat balance)) :: withdrawals) :: frame).
  Proof.
    intros negative tx old_state bound_data balance new_state recipient deposits withdrawals frame HV HB HU HP.
    assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; lia).
    assert (HA : Z.to_nat (Z.abs balance) = Z.to_nat balance) by (rewrite Z.abs_eq; lia).
    rewrite (verify_prefix_step negative 89).
    rewrite (verify_some_frame tx old_state bound_data balance new_state) by exact HV.
    rewrite (verified_numeric_prefix_step negative 79).
    rewrite HG, HA.
    rewrite (withdrawal_branch_updates_exact_stack balance (Z.to_nat balance) bound_data recipient)
      by assumption. reflexivity.
  Qed.

  Theorem failed_verification_rejects_iteration_with :
    forall negative tx old_state deposits withdrawals frame,
    verify tx old_state = None ->
    run primitive 90 (iteration_with negative)
      (tx :: old_state :: deposits :: VList withdrawals :: frame) = None.
  Proof.
    intros negative tx old_state deposits withdrawals frame HV.
    rewrite (verify_prefix_step negative 89).
    rewrite verify_none_frame by exact HV. apply (verify_failure_step negative 85).
  Qed.

  Corollary verified_positive_iteration_updates_exact_stack :
    forall tx old_state bound_data balance new_state recipient deposits withdrawals frame,
    verify tx old_state = Some (bound_data, balance, new_state) -> 0 < balance ->
    unpack bound_data = Some recipient -> List.length (pack recipient) = 28%nat ->
    run primitive 90 positive_iteration (tx :: old_state :: deposits :: VList withdrawals :: frame) =
    Some (new_state :: deposits :: VList (VPair recipient (VNat (Z.to_nat balance)) :: withdrawals) :: frame).
  Proof. intros; eapply verified_positive_iteration_with_updates_exact_stack; eassumption. Qed.
  Corollary failed_verification_rejects_iteration : forall tx old_state deposits withdrawals frame,
    verify tx old_state = None ->
    run primitive 90 positive_iteration (tx :: old_state :: deposits :: VList withdrawals :: frame) = None.
  Proof. intros; eapply failed_verification_rejects_iteration_with; eassumption. Qed.

  (* Common structural fuel for composition; it does not bound ITER length. *)
  Theorem verified_positive_iteration_128 :
    forall negative tx old_state bound_data balance new_state recipient deposits withdrawals frame,
    verify tx old_state = Some (bound_data, balance, new_state) -> 0 < balance ->
    unpack bound_data = Some recipient -> List.length (pack recipient) = 28%nat ->
    run primitive 128 (iteration_with negative)
      (tx :: old_state :: deposits :: VList withdrawals :: frame) =
    Some (new_state :: deposits :: VList (VPair recipient (VNat (Z.to_nat balance)) :: withdrawals) :: frame).
  Proof.
    intros negative tx old_state bound_data balance new_state recipient deposits withdrawals frame HV HB HU HP.
    assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; lia).
    assert (HA : Z.to_nat (Z.abs balance) = Z.to_nat balance) by (rewrite Z.abs_eq; lia).
    rewrite (verify_prefix_step negative 127).
    rewrite (verify_some_frame tx old_state bound_data balance new_state) by exact HV.
    rewrite (verified_numeric_prefix_step negative 117), HG, HA.
    rewrite (withdrawal_branch_updates_exact_stack_fuel 101 balance (Z.to_nat balance) bound_data recipient)
      by assumption. reflexivity.
  Qed.

  Theorem verified_positive_noncanonical_rejects_128 :
    forall negative tx old_state bound_data balance new_state recipient deposits withdrawals frame,
    verify tx old_state = Some (bound_data, balance, new_state) -> 0 < balance ->
    unpack bound_data = Some recipient -> List.length (pack recipient) <> 28%nat ->
    run primitive 128 (iteration_with negative)
      (tx :: old_state :: deposits :: VList withdrawals :: frame) = None.
  Proof.
    intros negative tx old_state bound_data balance new_state recipient deposits withdrawals frame HV HB HU HP.
    assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; lia).
    rewrite (verify_prefix_step negative 127).
    rewrite (verify_some_frame tx old_state bound_data balance new_state) by exact HV.
    rewrite (verified_numeric_prefix_step negative 117), HG.
    rewrite (withdrawal_branch_rejects_noncanonical_length_fuel 101 balance
      (Z.to_nat (Z.abs balance)) bound_data recipient) by assumption. reflexivity.
  Qed.

  Theorem failed_verification_rejects_iteration_128 :
    forall negative tx old_state deposits withdrawals frame,
    verify tx old_state = None ->
    run primitive 128 (iteration_with negative)
      (tx :: old_state :: deposits :: VList withdrawals :: frame) = None.
  Proof.
    intros negative tx old_state deposits withdrawals frame HV.
    rewrite (verify_prefix_step negative 127), verify_none_frame by exact HV.
    apply (verify_failure_step negative 123).
  Qed.
End PositiveFA2Path.

Print Assumptions withdrawal_branch_updates_exact_stack.
Print Assumptions withdrawal_branch_rejects_bad_unpack.
Print Assumptions verified_positive_iteration_updates_exact_stack.
Print Assumptions verified_positive_iteration_with_updates_exact_stack.
Print Assumptions failed_verification_rejects_iteration.
Print Assumptions verified_positive_iteration_128.
Print Assumptions verified_positive_noncanonical_rejects_128.
Print Assumptions failed_verification_rejects_iteration_128.
