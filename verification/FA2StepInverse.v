From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2LoopBody FA2DepositBody FA2Combined FA2Environment FA2MixedBatch.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* FA2 successful-step inverse for the complete concrete dispatch environment.
   Sapling results have byte-valued bound data. Callback meanings and their
   refinement to the protocol remain explicit external obligations. *)
Inductive step_event
  (verify : value -> value -> option (value * Z * value))
  (unpack : value -> option value) (pack : value -> list nat)
  (sender : value) (lookup : value -> value -> option nat)
  (update : value -> option nat -> value -> value) :
  value -> value -> value -> list value -> value -> value -> list value -> Prop :=
| event_positive : forall tx old map ws bound balance next recipient,
    verify tx old = Some (bound,balance,next) -> 0 < balance ->
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    step_event verify unpack pack sender lookup update tx old map ws next map
      (VPair recipient (VNat (Z.to_nat balance)) :: ws)
| event_negative : forall tx old map ws balance next,
    verify tx old = Some (VBytes [],balance,next) -> balance < 0 ->
    step_event verify unpack pack sender lookup update tx old map ws next
      (update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map) ws
| event_zero : forall tx old map ws next,
    verify tx old = Some (VBytes [],0,next) ->
    step_event verify unpack pack sender lookup update tx old map ws next map ws.

Section Inverse.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable other : string -> stack -> option stack.
  Variable frame : stack.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Hypothesis verify_bound_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.

  Lemma verify_some : forall tx old bound balance next rest,
    verify tx old = Some (bound,balance,next) ->
    prim "SAPLING_VERIFY_UPDATE" (tx::old::rest) =
      Some (VSome (VPair bound (VPair (VInt balance) next))::rest).
  Proof. intros; unfold prim; rewrite FA2Environment.verify_frame, H; reflexivity. Qed.
  Lemma verify_none : forall tx old rest,
    verify tx old = None -> prim "SAPLING_VERIFY_UPDATE" (tx::old::rest) = Some (VNone::rest).
  Proof. intros; unfold prim; rewrite FA2Environment.verify_frame, H; reflexivity. Qed.
  Lemma unpack_some : forall bound recipient rest,
    unpack bound = Some recipient -> prim "UNPACK_address" (bound::rest) = Some (VSome recipient::rest).
  Proof. intros; unfold prim; rewrite FA2Environment.unpack_frame, H; reflexivity. Qed.
  Lemma unpack_none : forall bound rest,
    unpack bound = None -> prim "UNPACK_address" (bound::rest) = Some (VNone::rest).
  Proof. intros; unfold prim; rewrite FA2Environment.unpack_frame, H; reflexivity. Qed.
  Lemma pack_frame : forall recipient rest,
    prim "PACK_address" (recipient::rest) = Some (VBytes (pack recipient)::rest).
  Proof. intros; unfold prim; apply FA2Environment.pack_frame. Qed.
  Lemma sender_frame : forall rest, prim "SENDER" rest = Some (sender::rest).
  Proof. intros; unfold prim; apply FA2Environment.sender_frame. Qed.
  Lemma get_frame : forall map rest,
    prim "GET" (sender::map::rest) = Some (FA2DepositBody.option_nat (lookup sender map)::rest).
  Proof. intros; unfold prim; rewrite FA2Environment.get_frame; destruct (lookup sender map); reflexivity. Qed.
  Lemma update_frame : forall map amount rest,
    prim "UPDATE" (sender::VSome (VNat amount)::map::rest) =
      Some (update sender (Some amount) map::rest).
  Proof. intros; unfold prim; apply FA2Environment.update_frame. Qed.

  Lemma positive_unpack_none_rejects : forall tx old bound balance next map ws,
    verify tx old = Some (bound,balance,next) -> 0 < balance -> unpack bound = None ->
    run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) = None.
  Proof.
    intros tx old bound balance next map ws HV HB HU.
    assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; lia).
    unfold FA2Combined.canonical_iteration.
    rewrite (FA2LoopBody.verify_prefix_step prim FA2DepositBody.nonpositive_branch 127),
      (verify_some tx old bound balance next) by exact HV.
    rewrite (FA2LoopBody.verified_numeric_prefix_step prim FA2DepositBody.nonpositive_branch 117), HG.
    rewrite (FA2LoopBody.unpack_prefix_step prim 115), (unpack_none bound) by exact HU.
    assert (BAD : run prim 115 FA2LoopBody.unpacked_tail
      (VNone :: VNat (Z.to_nat (Z.abs balance)) :: next :: map :: VList ws :: frame) = None).
    { exact (FA2LoopBody.unpack_failure_step prim 111 (Z.to_nat (Z.abs balance)) next map ws frame). }
    rewrite BAD. reflexivity.
  Qed.

  Local Opaque run.

  Theorem successful_step_extracts_event : forall tx old map ws result,
    run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) = Some result ->
    exists next map' ws',
      result = next::map'::VList ws'::frame /\
      step_event verify unpack pack sender lookup update tx old map ws next map' ws'.
  Proof.
    intros tx old map ws result Hrun.
    destruct (verify tx old) as [[[bound balance] next]|] eqn:HV.
    2: { assert (BAD : run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) = None).
         { unfold FA2Combined.canonical_iteration.
           eapply (FA2LoopBody.failed_verification_rejects_iteration_128 verify prim verify_none); eauto. }
         rewrite BAD in Hrun; discriminate. }
    destruct (verify_bound_bytes tx old bound balance next HV) as [bytes HB]; subst bound.
    destruct (Z_lt_dec 0 balance) as [Hpos|Hnon].
    - destruct (unpack (VBytes bytes)) as [recipient|] eqn:HU.
      2: { rewrite (positive_unpack_none_rejects tx old (VBytes bytes) balance next map ws HV Hpos HU) in Hrun; discriminate. }
      destruct (Nat.eq_dec (List.length (pack recipient)) 28) as [HP|HP].
      2: { assert (BAD : run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) = None).
           { unfold FA2Combined.canonical_iteration.
             eapply (FA2LoopBody.verified_positive_noncanonical_rejects_128 verify unpack pack prim unpack_some pack_frame verify_some); eauto. }
           rewrite BAD in Hrun; discriminate. }
      assert (STEP : run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) =
        Some (next::map::VList (VPair recipient (VNat (Z.to_nat balance))::ws)::frame)).
      { unfold FA2Combined.canonical_iteration.
        eapply (FA2LoopBody.verified_positive_iteration_128 verify unpack pack prim unpack_some pack_frame verify_some); eauto. }
      rewrite STEP in Hrun; inversion Hrun; subst result.
      exists next, map, (VPair recipient (VNat (Z.to_nat balance))::ws).
      split; [reflexivity|]. eapply event_positive; eauto.
    - destruct bytes as [|byte bytes].
      2: { assert (BAD : run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) = None).
           { unfold FA2Combined.canonical_iteration.
             eapply (FA2DepositBody.verified_nonpositive_nonempty_rejects_128 prim verify verify_some); eauto; lia. }
           rewrite BAD in Hrun; discriminate. }
      destruct (Z_lt_dec balance 0) as [Hneg|Hzero].
      + assert (STEP : run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) =
          Some (next::update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map::VList ws::frame)).
        { unfold FA2Combined.canonical_iteration.
          eapply (FA2DepositBody.verified_negative_iteration_128 sender lookup update prim verify sender_frame get_frame update_frame verify_some); eauto. }
        rewrite STEP in Hrun; inversion Hrun; subst result.
        exists next, (update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map), ws.
        split; [reflexivity|]. eapply event_negative; eauto.
      + assert (balance = 0) by lia; subst balance.
        assert (STEP : run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame) =
          Some (next::map::VList ws::frame)).
        { unfold FA2Combined.canonical_iteration.
          eapply (FA2DepositBody.verified_zero_iteration_128 prim verify verify_some); eauto. }
        rewrite STEP in Hrun; inversion Hrun; subst result.
        exists next, map, ws. split; [reflexivity|]. eapply event_zero; eauto.
  Qed.

  Theorem successful_loop_extracts_trace : forall txs old map ws result,
    iterate (fun tx st => run prim 128 FA2Combined.canonical_iteration (tx :: st))
      txs (old :: map :: VList ws :: frame) = Some result ->
    exists final finalmap finalws,
      result = final :: finalmap :: VList finalws :: frame /\
      FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
        txs old map ws final finalmap finalws.
  Proof.
    induction txs as [|tx txs IH]; intros old map ws result H.
    - cbn [iterate] in H. inversion H; subst.
      exists old, map, ws. split; [reflexivity|constructor].
    - cbn [iterate] in H.
      destruct (run prim 128 FA2Combined.canonical_iteration (tx::old::map::VList ws::frame)) as [step|] eqn:HS;
        [|discriminate].
      destruct (successful_step_extracts_event tx old map ws step HS) as [next [map' [ws' [E HE]]]].
      subst step.
      destruct (IH next map' ws' result H) as [final [finalmap [finalws [ER HT]]]].
      exists final, finalmap, finalws. split; [exact ER|].
      inversion HE; subst.
      + eapply FA2MixedBatch.mixed_positive; eauto.
      + eapply FA2MixedBatch.mixed_negative; eauto.
      + eapply FA2MixedBatch.mixed_zero; eauto.
  Qed.
End Inverse.
Print Assumptions successful_step_extracts_event.
Print Assumptions successful_loop_extracts_trace.
