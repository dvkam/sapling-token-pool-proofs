(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA12MixedBatch AssetLedger SaplingNotes
  TicketMixedBatch TicketInit FA2SenderMap FA2PublicSuccess FA2Operations.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Section FA12Backing.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable pool sender handle : value.
  Variable operation : value -> value -> value.
  Variable decode_call : value -> option (value * value).
  Hypothesis operation_fields : forall parameter handle,
    decode_call (operation parameter handle) = Some (handle,parameter).
  (* To discharge from the platform calling context and non-self source
     emission, not as an assumed final asset-safety conclusion. *)
  Hypothesis sender_is_not_pool : sender <> pool.
  Variable represents : value -> list note -> Prop.
  Hypothesis note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists next_notes, represents next next_notes /\ note_transition notes next_notes balance.

  Let decode := decode_fa12_operations eq_value decode_call handle.
  Let delta := net_delta eq_value pool.

  (* The trace is obtained from successful actual-program execution by the
     existing success converse. Here we refine its exact operation values,
     rather than defining reserves to follow the transaction balance. *)
  Theorem fa12_source_trace_pending_margin :
    forall txs initial ds ws final finalds finalws,
    mixed_trace verify unpack pack pool sender handle operation
      txs initial ds ws final finalds finalws ->
    forall notes dtrans wtrans,
    represents initial notes -> decode ds = Some dtrans -> decode ws = Some wtrans ->
    exists finalnotes finaldtrans finalwtrans,
      represents final finalnotes /\ decode finalds = Some finaldtrans /\
      decode finalws = Some finalwtrans /\
      delta finaldtrans + delta finalwtrans - liability finalnotes >=
      delta dtrans + delta wtrans - liability notes.
  Proof.
    intros txs initial ds ws final finalds finalws TRACE.
    induction TRACE as
      [state ds ws
      |tx txs old ds ws bound balance next recipient final fds fws HV HB HU HL HT IH
      |tx txs old ds ws balance next final fds fws HV HB HT IH
      |tx txs old ds ws next final fds fws HV HT IH];
      intros notes dtrans wtrans HR HD HW.
    - exists notes,dtrans,wtrans. repeat split; try assumption; lia.
    - destruct (note_soundness _ _ _ _ _ _ HV HR) as [ns [HN HNstep]].
      assert (DW : decode
        (operation (VPair pool (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws) =
        Some (Transfer pool recipient (Z.to_nat balance) :: wtrans)).
      { exact (decode_fa12_cons eq_value operation decode_call operation_fields handle
          (Transfer pool recipient (Z.to_nat balance)) ws wtrans HW). }
      destruct (IH ns dtrans _ HN HD DW) as [fn [fd [fw [HF [HFD [HFW HM]]]]]].
      exists fn,fd,fw. repeat split; try assumption.
      pose proof (note_transition_liability _ _ _ HNstep) as LN.
      pose proof (withdrawal_delta_lower_bound eq_value pool recipient (Z.to_nat balance)) as LD.
      unfold delta in *. cbn [net_delta] in HM. rewrite Z2Nat.id in LD by lia. lia.
    - destruct (note_soundness _ _ _ _ _ _ HV HR) as [ns [HN HNstep]].
      assert (DD : decode
        (operation (VPair sender (VPair pool (VNat (Z.to_nat (Z.abs balance))))) handle :: ds) =
        Some (Transfer sender pool (Z.to_nat (Z.abs balance)) :: dtrans)).
      { exact (decode_fa12_cons eq_value operation decode_call operation_fields handle
          (Transfer sender pool (Z.to_nat (Z.abs balance))) ds dtrans HD). }
      destruct (IH ns _ wtrans HN DD HW) as [fn [fd [fw [HF [HFD [HFW HM]]]]]].
      exists fn,fd,fw. repeat split; try assumption.
      pose proof (note_transition_liability _ _ _ HNstep) as LN.
      unfold delta in *. cbn [net_delta] in HM.
      rewrite deposit_delta in HM by exact sender_is_not_pool.
      rewrite Z2Nat.id in HM by apply Z.abs_nonneg. rewrite Z.abs_neq in HM by lia. lia.
    - destruct (note_soundness _ _ _ _ _ _ HV HR) as [ns [HN HNstep]].
      destruct (IH ns dtrans wtrans HN HD HW) as [fn [fd [fw [HF [HFD [HFW HM]]]]]].
      exists fn,fd,fw. repeat split; try assumption.
      pose proof (note_transition_liability _ _ _ HNstep). lia.
  Qed.

  Theorem fa12_emitted_operations_cover_liability_change :
    forall txs initial final finalds finalws notes,
    mixed_trace verify unpack pack pool sender handle operation
      txs initial [] [] final finalds finalws -> represents initial notes ->
    exists finalnotes transfers,
      represents final finalnotes /\
      decode (rev finalds ++ rev finalws) = Some transfers /\
      delta transfers >= liability finalnotes - liability notes.
  Proof.
    intros txs initial final finalds finalws notes HT HR.
    destruct (fa12_source_trace_pending_margin _ _ _ _ _ _ _ HT notes [] [] HR eq_refl eq_refl)
      as [fn [fd [fw [HF [HD [HW HM]]]]]].
    exists fn,(rev fd ++ rev fw). split; [exact HF|]. split.
    - apply (decode_fa12_app eq_value decode_call handle);
        apply (decode_fa12_rev eq_value decode_call handle); assumption.
    - unfold delta in *. rewrite net_delta_app, !net_delta_rev.
      cbn [net_delta] in HM. lia.
  Qed.

  (* This boundary may be instantiated by atomic call-tree settlement. It
     allows intermediate undercollateralization; only final real balances
     occur in the conclusion. No callback states the backing conclusion. *)
  Theorem committed_fa12_backing :
    forall txs initial final finalds finalws notes finalnotes transfers
      (before after : ledger),
    mixed_trace verify unpack pack pool sender handle operation
      txs initial [] [] final finalds finalws -> represents initial notes ->
    represents final finalnotes ->
    (forall a b, represents final a -> represents final b -> liability a = liability b) ->
    decode (rev finalds ++ rev finalws) = Some transfers ->
    after pool = before pool + delta transfers ->
    liability notes <= before pool -> liability finalnotes <= after pool.
  Proof.
    intros txs initial final finalds finalws notes finalnotes transfers before after
      HT HR HF Hunique Hdecode Hsettle Hinitial.
    destruct (fa12_emitted_operations_cover_liability_change _ _ _ _ _ _ HT HR)
      as [fn [ts [HN [HD HM]]]].
    rewrite Hdecode in HD. inversion HD; subst ts.
    pose proof (Hunique _ _ HF HN). lia.
  Qed.
End FA12Backing.
Print Assumptions fa12_source_trace_pending_margin.
Print Assumptions fa12_emitted_operations_cover_liability_change.
Print Assumptions committed_fa12_backing.

Section TicketBacking.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack handle : value -> option value.
  Variable operation : value -> value -> value.
  Variable issuer contents : value.
  Variable represents : value -> list note -> Prop.
  Hypothesis note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists next_notes, represents next next_notes /\ note_transition notes next_notes balance.

  Theorem ticket_source_trace_live_note_accounting :
    forall txs old held credit ops next finalheld finalcredit finalops total,
    ticket_trace verify unpack handle operation issuer contents
      txs old held credit ops next finalheld finalcredit finalops total ->
    forall notes, represents old notes -> exists finalnotes,
      represents next finalnotes /\ liability finalnotes = liability notes - total.
  Proof.
    intros txs old held credit ops next finalheld finalcredit finalops total HT.
    induction HT; intros notes HR.
    - exists notes; split; [exact HR|lia].
    - destruct (note_soundness _ _ _ _ _ _ H HR) as [ns [HN HS]].
      destruct (IHHT ns HN) as [fn [HF HL]]. exists fn; split; [exact HF|].
      pose proof (note_transition_liability _ _ _ HS); lia.
    - destruct (note_soundness _ _ _ _ _ _ H HR) as [ns [HN HS]].
      destruct (IHHT ns HN) as [fn [HF HL]]. exists fn; split; [exact HF|].
      pose proof (note_transition_liability _ _ _ HS); lia.
    - destruct (note_soundness _ _ _ _ _ _ H HR) as [ns [HN HS]].
      destruct (IHHT ns HN) as [fn [HF HL]]. exists fn; split; [exact HF|].
      pose proof (note_transition_liability _ _ _ HS); lia.
  Qed.

  (* The quantity equation is DERIVED by the whole-source converse, including
     zero final incoming credit. Without that guard, paid tickets could leave
     unmatched credit; using old reserve alone would be unjustified. *)
  Theorem source_held_quantity_backs_final_notes :
    forall txs old held credit ops next finalheld finalcredit finalops total notes old_quantity,
    ticket_trace verify unpack handle operation issuer contents
      txs old held credit ops next finalheld finalcredit finalops total ->
    represents old notes -> liability notes <= Z.of_nat old_quantity ->
    Z.of_nat old_quantity - total = Z.of_nat (held_quantity finalheld) ->
    exists finalnotes, represents next finalnotes /\
      liability finalnotes <= Z.of_nat (held_quantity finalheld).
  Proof.
    intros. destruct (ticket_source_trace_live_note_accounting txs old held credit ops
      next finalheld finalcredit finalops total H notes H0)
      as [fn [HF HE]]. exists fn; split; [exact HF|lia].
  Qed.
End TicketBacking.

(* Actual ticket ownership is a resource/context fact, not an equality we
   assume between a scalar storage field and all the pool's collateral.
   A certified stored fragment gives a lower bound; extra owned fragments
   of the same full asset legitimately yield surplus. Native linearity and
   ticket-balance-table refinement must establish this certificate. *)
Record owned_fragment := OwnedFragment {
  fragment_id : nat; owner : value; ticketer : value; payload : value; quantity : nat
}.
Section TicketOwnership.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Definition fragment_reserve (pool issuer contents : value) (f : owned_fragment) : Z :=
    if eq_value (owner f) pool then
      if eq_value (ticketer f) issuer then
        if eq_value (payload f) contents then Z.of_nat (quantity f) else 0
      else 0 else 0.
  Fixpoint owned_reserve pool issuer contents (inventory : list owned_fragment) : Z :=
    match inventory with [] => 0 | f :: rest =>
      fragment_reserve pool issuer contents f + owned_reserve pool issuer contents rest end.
  Definition valid_inventory inventory := NoDup (map fragment_id inventory).
  Lemma fragment_reserve_nonnegative : forall pool issuer contents f,
    0 <= fragment_reserve pool issuer contents f.
  Proof.
    intros; unfold fragment_reserve.
    repeat match goal with |- context [eq_value ?a ?b] => destruct (eq_value a b) end; lia.
  Qed.
  Lemma owned_reserve_nonnegative : forall pool issuer contents inventory,
    0 <= owned_reserve pool issuer contents inventory.
  Proof.
    intros pool issuer contents inventory; induction inventory; cbn [owned_reserve]; [lia|].
    pose proof (fragment_reserve_nonnegative pool issuer contents a); lia.
  Qed.
  Theorem certified_held_fragment_bounds_actual_reserve :
    forall pool issuer contents inventory f,
    In f inventory -> owner f = pool -> ticketer f = issuer -> payload f = contents ->
    Z.of_nat (quantity f) <= owned_reserve pool issuer contents inventory.
  Proof.
    intros pool issuer contents inventory; induction inventory as [|a rest IH];
      intros f HIN HO HI HC; [contradiction|].
    cbn [owned_reserve]. destruct HIN as [E|HIN].
    - subst a. unfold fragment_reserve at 1. rewrite HO,HI,HC.
      destruct (eq_value pool pool); [|contradiction].
      destruct (eq_value issuer issuer); [|contradiction].
      destruct (eq_value contents contents); [|contradiction].
      pose proof (owned_reserve_nonnegative pool issuer contents rest); lia.
    - specialize (IH f HIN HO HI HC).
      pose proof (fragment_reserve_nonnegative pool issuer contents a); lia.
  Qed.
  Theorem owned_ticket_reserve_backs_stored_liability :
    forall pool issuer contents inventory f notes,
    In f inventory -> owner f = pool -> ticketer f = issuer -> payload f = contents ->
    liability notes <= Z.of_nat (quantity f) ->
    liability notes <= owned_reserve pool issuer contents inventory.
  Proof.
    intros. pose proof (certified_held_fragment_bounds_actual_reserve _ _ _ _ _ H H0 H1 H2). lia.
  Qed.
End TicketOwnership.
Print Assumptions ticket_source_trace_live_note_accounting.
Print Assumptions owned_ticket_reserve_backs_stored_liability.

Section FA2Backing.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable pool sender token_id : value.
  Hypothesis sender_is_not_pool : sender <> pool.
  Variable represents : value -> list note -> Prop.
  Hypothesis note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists next_notes, represents next next_notes /\ note_transition notes next_notes balance.
  Definition quantity_pairs (xs : list (value * nat)) :=
    map (fun '(account,q) => (account,VNat q)) xs.
  Definition withdrawal_values (xs : list (value * nat)) :=
    map (fun '(account,q) => VPair account (VNat q)) xs.
  Let delta := net_delta eq_value pool.

  Theorem fa2_counted_trace_pending_margin :
    forall txs old m ws final fm fws sum,
    FA2SenderMap.counted_trace sender eq_value verify unpack pack
      txs old m ws final fm fws sum ->
    forall notes withdrawals,
    represents old notes -> ws = withdrawal_values withdrawals ->
    exists finalnotes finalwithdrawals,
      represents final finalnotes /\ fws = withdrawal_values finalwithdrawals /\
      Z.of_nat sum + delta (movements pool finalwithdrawals) - liability finalnotes >=
      delta (movements pool withdrawals) - liability notes.
  Proof.
    intros txs old m ws final fm fws sum HT.
    induction HT as
      [state m ws
      |tx txs old m ws bound balance next recipient final fm fws sum HV HB HU HL HT IH
      |tx txs old m ws balance next final fm fws sum HV HB HT IH
      |tx txs old m ws next final fm fws sum HV HT IH];
      intros notes withdrawals HR HW.
    - exists notes,withdrawals. repeat split; try assumption; lia.
    - destruct (note_soundness _ _ _ _ _ _ HV HR) as [ns [HN HS]].
      assert (HWS : VPair recipient (VNat (Z.to_nat balance)) :: ws =
        withdrawal_values ((recipient,Z.to_nat balance)::withdrawals)).
      { cbn [withdrawal_values map]; now rewrite HW. }
      destruct (IH ns _ HN HWS) as [fn [fw [HF [HFW HM]]]].
      exists fn,fw. repeat split; try assumption.
      pose proof (note_transition_liability _ _ _ HS) as LN.
      pose proof (withdrawal_delta_lower_bound eq_value pool recipient (Z.to_nat balance)) as LD.
      unfold delta, movements in *. cbn [map net_delta] in HM.
      rewrite Z2Nat.id in LD by lia. lia.
    - destruct (note_soundness _ _ _ _ _ _ HV HR) as [ns [HN HS]].
      destruct (IH ns withdrawals HN HW) as [fn [fw [HF [HFW HM]]]].
      exists fn,fw. repeat split; try assumption.
      pose proof (note_transition_liability _ _ _ HS) as LN.
      rewrite Nat2Z.inj_add, Z2Nat.id by apply Z.abs_nonneg.
      rewrite Z.abs_neq by lia. lia.
    - destruct (note_soundness _ _ _ _ _ _ HV HR) as [ns [HN HS]].
      destruct (IH ns withdrawals HN HW) as [fn [fw [HF [HFW HM]]]].
      exists fn,fw. repeat split; try assumption.
      pose proof (note_transition_liability _ _ _ HS); lia.
  Qed.

  Lemma source_transfer_groups_equal_exact_encoded_groups : forall deposits withdrawals,
    FA2PublicSuccess.transfer_groups pool token_id (quantity_pairs deposits) (quantity_pairs withdrawals) =
      fa2_deposit_groups token_id pool deposits ++ [VPair pool (VList (fa2_items token_id withdrawals))].
  Proof.
    intros. unfold FA2PublicSuccess.transfer_groups, FA2PublicSuccess.withdrawal_items,
      quantity_pairs, fa2_deposit_groups, fa2_items.
    rewrite !map_map. f_equal.
    - apply map_ext. intros [payer q]. reflexivity.
    - f_equal. f_equal. f_equal. apply map_ext. intros [recipient q]. reflexivity.
  Qed.

  Theorem fa2_public_parameter_decodes_exact_movements : forall deposits withdrawals,
    decode_fa2_parameter eq_value token_id
      (VList (FA2PublicSuccess.transfer_groups pool token_id
        (quantity_pairs deposits) (quantity_pairs withdrawals))) =
    Some (deposit_movements pool deposits ++ movements pool withdrawals).
  Proof.
    intros. rewrite source_transfer_groups_equal_exact_encoded_groups.
    apply decode_fa2_deposit_first_parameter.
  Qed.

  Lemma quantity_pairs_rev : forall xs, quantity_pairs (rev xs) = rev (quantity_pairs xs).
  Proof. intros; unfold quantity_pairs; apply map_rev. Qed.

  Lemma quantity_pairs_injective : forall xs ys, quantity_pairs xs = quantity_pairs ys -> xs = ys.
  Proof.
    induction xs as [|[x q] xs IH]; intros [|[y r] ys] H; cbn [quantity_pairs map] in H;
      try discriminate; [reflexivity|]. inversion H; subst. f_equal.
    apply IH. assumption.
  Qed.
  Lemma withdrawal_values_injective : forall xs ys, withdrawal_values xs = withdrawal_values ys -> xs = ys.
  Proof.
    induction xs as [|[x q] xs IH]; intros [|[y r] ys] H; cbn [withdrawal_values map] in H;
      try discriminate; [reflexivity|]. inversion H; subst. f_equal.
    apply IH. assumption.
  Qed.

  (* From the exact source-derived counted trace and its initially empty
     map, reconstruct the actual typed FA2 parameter and all its movements.
     A singleton sender map is proved reachable; no generic map shape or
     deposit-sum conclusion is assumed as a collateral premise. *)
  Theorem fa2_source_public_movements_cover_liability_change :
    forall txs initial final fm fws sum notes,
    FA2SenderMap.counted_trace sender eq_value verify unpack pack
      txs initial (VMap []) [] final fm fws sum -> represents initial notes ->
    exists finalnotes deposits withdrawals,
      represents final finalnotes /\ fm = VMap (quantity_pairs deposits) /\
      fws = withdrawal_values withdrawals /\
      decode_fa2_parameter eq_value token_id
        (VList (FA2PublicSuccess.transfer_groups pool token_id
          (quantity_pairs deposits) (quantity_pairs (rev withdrawals)))) =
        Some (deposit_movements pool deposits ++ movements pool (rev withdrawals)) /\
      delta (deposit_movements pool deposits ++ movements pool (rev withdrawals)) >=
        liability finalnotes - liability notes.
  Proof.
    intros txs initial final fm fws sum notes HT HR.
    destruct (fa2_counted_trace_pending_margin _ _ _ _ _ _ _ _ HT notes [] HR eq_refl)
      as [fn [fw [HF [HFW HM]]]].
    pose proof (FA2SenderMap.reachable_sender_deposit_sum sender eq_value
      verify unpack pack _ _ _ _ _ _ _ _ HT (or_introl eq_refl)) as [HS HA].
    assert (HREV : delta (movements pool (rev fw)) = delta (movements pool fw)).
    { unfold delta,movements. rewrite map_rev. apply net_delta_rev. }
    change (Z.of_nat sum + delta (movements pool fw) - liability fn >=
      0 - liability notes) in HM.
    destruct HS as [HE|[n HE]]; subst fm.
    - cbn [FA2SenderMap.amount] in HA.
      exists fn,[],fw. repeat split; try assumption; try reflexivity.
      + apply fa2_public_parameter_decodes_exact_movements.
      + unfold delta. rewrite net_delta_app. cbn [deposit_movements map net_delta].
        fold delta. rewrite HREV. assert (sum = 0%nat) by lia. subst; cbn in HM; lia.
    - cbn [FA2SenderMap.amount] in HA.
      exists fn,[(sender,n)],fw. repeat split; try assumption; try reflexivity.
      + apply fa2_public_parameter_decodes_exact_movements.
      + unfold delta. rewrite net_delta_app. cbn [deposit_movements map net_delta].
        rewrite deposit_delta by exact sender_is_not_pool.
         fold delta. rewrite HREV. rewrite HA. cbn [Nat.add]. lia.
  Qed.

  Theorem fa2_explicit_source_movements_cover_liability_change :
    forall txs initial final fm fws sum notes finalnotes deposits withdrawals,
    FA2SenderMap.counted_trace sender eq_value verify unpack pack
      txs initial (VMap []) [] final fm fws sum -> represents initial notes ->
    represents final finalnotes ->
    (forall a b, represents final a -> represents final b -> liability a = liability b) ->
    fm = VMap (quantity_pairs deposits) -> fws = withdrawal_values withdrawals ->
    delta (deposit_movements pool deposits ++ movements pool (rev withdrawals)) >=
      liability finalnotes - liability notes.
  Proof.
    intros txs initial final fm fws sum notes finalnotes deposits withdrawals
      HT HR HF Hunique HMAP HWS.
    destruct (fa2_source_public_movements_cover_liability_change _ _ _ _ _ _ _ HT HR)
      as [fn [ds [ws [HN [HM [HW [HD HL]]]]]]].
    rewrite HMAP in HM. inversion HM.
    assert (ds = deposits) by (apply quantity_pairs_injective; congruence).
    assert (ws = withdrawals) by (apply withdrawal_values_injective; congruence).
    subst ds ws. pose proof (Hunique _ _ HF HN). lia.
  Qed.
End FA2Backing.
Print Assumptions fa2_source_public_movements_cover_liability_change.
