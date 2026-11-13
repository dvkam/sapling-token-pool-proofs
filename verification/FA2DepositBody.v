From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP FA2Nonpositive FA2LoopBody.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* Exact nonpositive IF branch in the partial VM, with explicit sender,
   lookup and update callbacks. This proves key/quantity/stack plumbing;
   callback agreement with Michelson maps and Octez is not proved here.
   The incoming balance/amount/state are already the verified Sapling result.
   Gas, cryptography, asset behavior and rollback remain outside this model. *)
Section NonpositiveFA2Path.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable primitive : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).

  Definition option_nat (n : option nat) : value :=
    match n with None => VNone | Some x => VSome (VNat x) end.
  Definition balance_or_zero (n : option nat) : nat :=
    match n with None => 0%nat | Some x => x end.
  (* Explicit frame premises permit both paths to share one common concrete
     environment. Agreement of that environment with Octez remains separate. *)
  Hypothesis sender_frame : forall s, primitive "SENDER" s = Some (sender :: s).
  Hypothesis get_frame : forall map rest,
    primitive "GET" (sender :: map :: rest) = Some (option_nat (lookup sender map) :: rest).
  Hypothesis update_frame : forall map amount rest,
    primitive "UPDATE" (sender :: VSome (VNat amount) :: map :: rest) =
    Some (update sender (Some amount) map :: rest).
  Hypothesis verify_some_frame : forall tx old bound balance next rest,
    verify tx old = Some (bound, balance, next) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).

  Definition after_get : list instruction :=
    [IfNone [Push (VNat 0)] []; Add; Dig 2; Swap; SomeValue;
     Prim "SENDER"; Prim "UPDATE"; Swap].
  Definition deposit_body : list instruction :=
    [Dup 3; Prim "SENDER"; Prim "GET"] ++ after_get.
  Definition nonpositive_branch : list instruction :=
    bound_data_check ++ [IsLt; If deposit_body [Drop]].

  (* Symbolic-fuel equations avoid reducing a continuation on an unknown
     callback result. The equations themselves are checked by conversion. *)
  Lemma sender_prefix_step : forall fuel amount state map ws frame,
    run primitive (2 + fuel)%nat deposit_body
      (VNat amount :: state :: map :: VList ws :: frame) =
    match primitive "SENDER" (map :: VNat amount :: state :: map :: VList ws :: frame) with
    | Some s => run primitive fuel (Prim "GET" :: after_get) s | None => None end.
  Proof. reflexivity. Qed.
  Lemma primitive_step : forall fuel name code s,
    run primitive (S fuel) (Prim name :: code) s =
    match primitive name s with Some next => run primitive fuel code next | None => None end.
  Proof. reflexivity. Qed.
  Lemma sum_prefix_step : forall fuel found amount state map ws frame,
    run primitive (6 + fuel)%nat after_get
      (option_nat found :: VNat amount :: state :: map :: VList ws :: frame) =
    match primitive "SENDER"
      (VSome (VNat ((balance_or_zero found + amount)%nat)) :: map :: state :: VList ws :: frame) with
    | Some s => run primitive fuel [Prim "UPDATE"; Swap] s | None => None end.
  Proof. intros; destruct found; reflexivity. Qed.
  Lemma final_swap_step : forall fuel next state ws frame,
    run primitive (2 + fuel)%nat [Swap] (next :: state :: VList ws :: frame) =
    Some (state :: next :: VList ws :: frame).
  Proof. reflexivity. Qed.
  Lemma nonpositive_prefix_step : forall fuel balance amount state map ws frame,
    run primitive (8 + S fuel)%nat nonpositive_branch
      (VInt balance :: VNat amount :: state :: VBytes [] :: map :: VList ws :: frame) =
    match run primitive (S fuel) (if Z.ltb balance 0 then deposit_body else [Drop])
      (VNat amount :: state :: map :: VList ws :: frame) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Lemma final_drop_step : forall fuel amount state map ws frame,
    run primitive (2 + fuel)%nat [Drop] (VNat amount :: state :: map :: VList ws :: frame) =
    Some (state :: map :: VList ws :: frame).
  Proof. reflexivity. Qed.
  Lemma nonempty_failure_step : forall fuel balance amount state byte bytes map ws frame,
    run primitive (10 + fuel)%nat nonpositive_branch
      (VInt balance :: VNat amount :: state :: VBytes (byte :: bytes) :: map :: VList ws :: frame) = None.
  Proof. reflexivity. Qed.
  Local Opaque run.

  Theorem deposit_body_updates_exact_stack_fuel : forall padding amount state map ws frame,
    run primitive (12 + padding)%nat deposit_body (VNat amount :: state :: map :: VList ws :: frame) =
    Some (state :: update sender (Some ((balance_or_zero (lookup sender map) + amount)%nat)) map :: VList ws :: frame).
  Proof.
    intros padding amount state map ws frame.
    rewrite (sender_prefix_step (10 + padding)%nat), sender_frame,
      (primitive_step (9 + padding)%nat), get_frame.
    rewrite (sum_prefix_step (3 + padding)%nat), sender_frame,
      (primitive_step (2 + padding)%nat), update_frame.
    apply (final_swap_step padding).
  Qed.

  Theorem negative_branch_updates_exact_stack_fuel : forall padding balance amount state map ws frame,
    balance < 0 ->
    run primitive (20 + padding)%nat nonpositive_branch
      (VInt balance :: VNat amount :: state :: VBytes [] :: map :: VList ws :: frame) =
    Some (state :: update sender (Some ((balance_or_zero (lookup sender map) + amount)%nat)) map :: VList ws :: frame).
  Proof.
    intros padding balance amount state map ws frame HB.
    assert (HL : Z.ltb balance 0 = true) by (apply Z.ltb_lt; lia).
    rewrite (nonpositive_prefix_step (11 + padding)%nat), HL,
      (deposit_body_updates_exact_stack_fuel padding). reflexivity.
  Qed.

  Theorem zero_branch_preserves_public_accumulators_fuel : forall padding state map ws frame,
    run primitive (20 + padding)%nat nonpositive_branch
      (VInt 0 :: VNat 0 :: state :: VBytes [] :: map :: VList ws :: frame) =
    Some (state :: map :: VList ws :: frame).
  Proof.
    intros padding state map ws frame. rewrite (nonpositive_prefix_step (11 + padding)%nat).
    change ((match run primitive (12 + padding)%nat [Drop]
      (VNat 0 :: state :: map :: VList ws :: frame) with
      Some s => Some s | None => None end) = Some (state :: map :: VList ws :: frame)).
    rewrite (final_drop_step (10 + padding)%nat). reflexivity.
  Qed.

  Theorem deposit_body_updates_exact_stack : forall amount state map ws frame,
    run primitive 80 deposit_body (VNat amount :: state :: map :: VList ws :: frame) =
    Some (state :: update sender (Some ((balance_or_zero (lookup sender map) + amount)%nat)) map ::
          VList ws :: frame).
  Proof.
    intros amount state map ws frame.
    rewrite (sender_prefix_step 78), sender_frame, (primitive_step 77), get_frame.
    rewrite (sum_prefix_step 71), sender_frame, (primitive_step 70), update_frame.
    apply (final_swap_step 68).
  Qed.

  Theorem negative_branch_updates_exact_stack : forall balance amount state map ws frame,
    balance < 0 ->
    run primitive 88 nonpositive_branch
      (VInt balance :: VNat amount :: state :: VBytes [] :: map :: VList ws :: frame) =
    Some (state :: update sender (Some ((balance_or_zero (lookup sender map) + amount)%nat)) map ::
          VList ws :: frame).
  Proof.
    intros balance amount state map ws frame HB.
    assert (HL : Z.ltb balance 0 = true) by (apply Z.ltb_lt; lia).
    rewrite (nonpositive_prefix_step 79), HL, deposit_body_updates_exact_stack. reflexivity.
  Qed.

  Theorem zero_branch_preserves_public_accumulators : forall state map ws frame,
    run primitive 88 nonpositive_branch
      (VInt 0 :: VNat 0 :: state :: VBytes [] :: map :: VList ws :: frame) =
    Some (state :: map :: VList ws :: frame).
  Proof.
    intros state map ws frame. rewrite (nonpositive_prefix_step 79).
    change ((match run primitive 80 [Drop] (VNat 0 :: state :: map :: VList ws :: frame) with
             Some s => Some s | None => None end) = Some (state :: map :: VList ws :: frame)).
    rewrite (final_drop_step 78). reflexivity.
  Qed.

  Theorem nonempty_bound_data_rejects_nonpositive_branch :
    forall balance amount state byte bytes map ws frame,
    run primitive 88 nonpositive_branch
      (VInt balance :: VNat amount :: state :: VBytes (byte :: bytes) :: map :: VList ws :: frame) = None.
  Proof. intros; apply (nonempty_failure_step 78). Qed.

  Theorem verified_negative_iteration_128 : forall tx old balance state map ws frame,
    verify tx old = Some (VBytes [], balance, state) -> balance < 0 ->
    run primitive 128 (FA2LoopBody.iteration_with nonpositive_branch)
      (tx :: old :: map :: VList ws :: frame) =
    Some (state :: update sender
      (Some ((balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map :: VList ws :: frame).
  Proof.
    intros tx old balance state map ws frame HV HB.
    assert (HG : Z.gtb balance 0 = false).
    { destruct (Z.gtb balance 0) eqn:HT; [apply Z.gtb_lt in HT; lia | reflexivity]. }
    rewrite (FA2LoopBody.verify_prefix_step primitive nonpositive_branch 127).
    rewrite (verify_some_frame tx old (VBytes []) balance state) by exact HV.
    rewrite (FA2LoopBody.verified_numeric_prefix_step primitive nonpositive_branch 117), HG.
    rewrite (negative_branch_updates_exact_stack_fuel 98) by exact HB. reflexivity.
  Qed.

  Theorem verified_zero_iteration_128 : forall tx old state map ws frame,
    verify tx old = Some (VBytes [], 0, state) ->
    run primitive 128 (FA2LoopBody.iteration_with nonpositive_branch)
      (tx :: old :: map :: VList ws :: frame) = Some (state :: map :: VList ws :: frame).
  Proof.
    intros tx old state map ws frame HV.
    rewrite (FA2LoopBody.verify_prefix_step primitive nonpositive_branch 127).
    rewrite (verify_some_frame tx old (VBytes []) 0 state) by exact HV.
    rewrite (FA2LoopBody.verified_numeric_prefix_step primitive nonpositive_branch 117).
    change ((match run primitive 118 nonpositive_branch
      (VInt 0 :: VNat 0 :: state :: VBytes [] :: map :: VList ws :: frame) with
      Some s => Some s | None => None end) = Some (state :: map :: VList ws :: frame)).
    rewrite (zero_branch_preserves_public_accumulators_fuel 98). reflexivity.
  Qed.

  Theorem verified_nonpositive_nonempty_rejects_128 :
    forall tx old balance state byte bytes map ws frame,
    verify tx old = Some (VBytes (byte :: bytes), balance, state) -> balance <= 0 ->
    run primitive 128 (FA2LoopBody.iteration_with nonpositive_branch)
      (tx :: old :: map :: VList ws :: frame) = None.
  Proof.
    intros tx old balance state byte bytes map ws frame HV HB.
    assert (HG : Z.gtb balance 0 = false).
    { destruct (Z.gtb balance 0) eqn:HT; [apply Z.gtb_lt in HT; lia | reflexivity]. }
    rewrite (FA2LoopBody.verify_prefix_step primitive nonpositive_branch 127).
    rewrite (verify_some_frame tx old (VBytes (byte :: bytes)) balance state) by exact HV.
    rewrite (FA2LoopBody.verified_numeric_prefix_step primitive nonpositive_branch 117), HG.
    rewrite (nonempty_failure_step 108). reflexivity.
  Qed.
End NonpositiveFA2Path.

Print Assumptions deposit_body_updates_exact_stack.
Print Assumptions negative_branch_updates_exact_stack.
Print Assumptions zero_branch_preserves_public_accumulators.
Print Assumptions nonempty_bound_data_rejects_nonpositive_branch.
Print Assumptions verified_negative_iteration_128.
Print Assumptions verified_zero_iteration_128.
Print Assumptions verified_nonpositive_nonempty_rejects_128.
