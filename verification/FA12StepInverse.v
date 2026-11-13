From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA12LoopBody FA12MixedBatch FA12LoopExtract FA12AddressGuardInverse.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Complete framed semantics on the typed FA1.2 transaction path. The
   verifier always returns byte-valued bound data or rejects. The callback
   equations are platform specifications, not consequences of success. *)
Section Inverse.
  Variable prim : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable self sender handle token : value.
  Variable operation : value -> value -> value.
  Variable frame : stack.
  Hypothesis verify_some : forall tx old bound balance next rest,
    verify tx old = Some (bound,balance,next) ->
    prim "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
      Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis verify_none : forall tx old rest,
    verify tx old = None ->
    prim "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) = Some (VNone :: rest).
  Hypothesis verify_bound_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.
  Hypothesis unpack_some : forall bound recipient rest,
    unpack bound = Some recipient ->
    prim "UNPACK_address" (bound :: rest) = Some (VSome recipient :: rest).
  Hypothesis unpack_none : forall bound rest,
    unpack bound = None -> prim "UNPACK_address" (bound :: rest) = Some (VNone :: rest).
  Hypothesis pack_frame : forall recipient rest,
    prim "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (self :: rest).
  Hypothesis sender_frame : forall rest, prim "SENDER" rest = Some (sender :: rest).
  Hypothesis operation_frame : forall parameters handle0 rest,
    prim "TRANSFER_TOKENS" (parameters :: VMutez 0 :: handle0 :: rest) =
    Some (operation parameters handle0 :: rest).

  Lemma verify_none_tail : forall fuel rest,
    run prim (4 + fuel)%nat (tl iteration) (VNone :: rest) = None.
  Proof. reflexivity. Qed.

  Lemma failed_verification_rejects : forall tx old ds ws,
    verify tx old = None ->
    run prim 128 iteration
      (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) = None.
  Proof.
    intros tx old ds ws H.
    rewrite (verify_step prim 127), (verify_none tx old) by exact H.
    apply (verify_none_tail 123).
  Qed.

  Lemma nonpositive_nonempty_rejects : forall tx old byte bytes balance next ds ws,
    verify tx old = Some (VBytes (byte::bytes),balance,next) ->
    balance <= 0 ->
    run prim 128 iteration
      (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) = None.
  Proof.
    intros tx old byte bytes balance next ds ws HV HB.
    assert (HG : Z.gtb balance 0 = false).
    { destruct (Z.gtb balance 0) eqn:E; [apply Z.gtb_lt in E; lia | reflexivity]. }
    rewrite (verify_step prim 127), (verify_some tx old (VBytes (byte::bytes)) balance next) by exact HV.
    rewrite (numeric_step prim 117), HG.
    rewrite (nonpositive_guard_step prim 117).
    rewrite (empty_guard_bad prim 110). reflexivity.
  Qed.

  Local Opaque run.

  Theorem successful_step_extracts_event : forall tx old ds ws result,
    run prim 128 iteration
      (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) = Some result ->
    exists next ds' ws',
      result = next :: handle :: token :: VPair (VList ds') (VList ws') :: frame /\
      step_event verify unpack pack self sender handle operation tx old ds ws next ds' ws'.
  Proof.
    intros tx old ds ws result Hrun.
    destruct (verify tx old) as [[[bound balance] next]|] eqn:HV.
    2: { rewrite (failed_verification_rejects tx old ds ws HV) in Hrun. discriminate. }
    destruct (verify_bound_bytes tx old bound balance next HV) as [bytes HB]; subst bound.
    destruct (Z_lt_dec 0 balance) as [Hpos|Hnon].
    - assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; lia).
      pose proof Hrun as HGd.
      rewrite (verify_step prim 127), (verify_some tx old (VBytes bytes) balance next) in HGd by exact HV.
      rewrite (numeric_step prim 117), HG in HGd.
      rewrite (positive_guard_step prim 116) in HGd.
      destruct (run prim 116 address_guard
        (VBytes bytes :: handle :: token :: VPair (VList ds) (VList ws) :: frame)) as [guarded|] eqn:Hguard;
        [|discriminate].
      destruct (FA12AddressGuardInverse.guard_success_inverse prim unpack pack unpack_some unpack_none pack_frame
        101 (VBytes bytes) (handle :: token :: VPair (VList ds) (VList ws) :: frame) guarded Hguard)
        as [recipient [HU [HP HE]]].
      assert (STEP : run prim 128 iteration
        (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
        Some (next :: handle :: token :: VPair (VList ds)
          (VList (operation (VPair self (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws)) :: frame)).
      { eapply FA12LoopBody.verified_positive_iteration_128; eauto. }
      rewrite STEP in Hrun. inversion Hrun; subst result.
      exists next, ds, (operation (VPair self (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws).
      split; [reflexivity|]. eapply event_positive; eauto.
    - destruct bytes as [|byte bytes].
      2: { rewrite (nonpositive_nonempty_rejects tx old byte bytes balance next ds ws HV) in Hrun by lia. discriminate. }
      destruct (Z_lt_dec balance 0) as [Hneg|Hzero].
      + assert (STEP : run prim 128 iteration
          (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
          Some (next :: handle :: token :: VPair
            (VList (operation (VPair sender (VPair self (VNat (Z.to_nat (Z.abs balance))))) handle :: ds)) (VList ws) :: frame)).
        { eapply FA12LoopBody.verified_negative_iteration_128; eauto. }
        rewrite STEP in Hrun. inversion Hrun; subst result.
        exists next, (operation (VPair sender (VPair self (VNat (Z.to_nat (Z.abs balance))))) handle :: ds), ws.
        split; [reflexivity|]. eapply event_negative; eauto.
      + assert (balance = 0) by lia. subst balance.
        assert (STEP : run prim 128 iteration
          (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
          Some (next :: handle :: token :: VPair (VList ds) (VList ws) :: frame)).
        { eapply FA12LoopBody.verified_zero_iteration_128; eauto. }
        rewrite STEP in Hrun. inversion Hrun; subst result.
        exists next, ds, ws. split; [reflexivity|]. eapply event_zero; eauto.
  Qed.

  Theorem successful_loop_extracts_trace : forall txs old ds ws result,
    iterate (fun tx st => run prim 128 iteration (tx :: st))
      txs (old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) = Some result ->
    exists final finalds finalws,
      result = final :: handle :: token :: VPair (VList finalds) (VList finalws) :: frame /\
      FA12MixedBatch.mixed_trace verify unpack pack self sender handle operation
        txs old ds ws final finalds finalws.
  Proof.
    intros txs old ds ws result H.
    eapply FA12LoopExtract.successful_iteration_extracts_trace; [|exact H].
    intros tx old0 ds0 ws0 result0 HS.
    eapply successful_step_extracts_event; eauto.
  Qed.
End Inverse.
Print Assumptions successful_step_extracts_event.
Print Assumptions successful_loop_extracts_trace.
