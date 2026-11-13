(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2Boundary FA2Environment FA2MixedBatch FA2SenderMap
  FA2PrivateSuccess FA2PublicSuccess FA2OutputInverse SourceLink.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* SourceLink checks the complete parsed program equality; source importer
   and modeled/protocol primitive correspondence remain trusted. *)
Require Import AssetLedger SaplingNotes PoolCollateral CollateralCallTree FA2ParsedInverse.
Section ParsedCollateral.
  Variable sender : value.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable other : string -> stack -> option stack.
  Variable amount : nat.
  Variable pool : value.
  Variable operation : value -> value -> value.
  Variable contract_lookup : value -> option value.
  Let lookup := FA2SenderMap.lookup eq_value.
  Let update := FA2SenderMap.update.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez amount :: rest).
  Hypothesis verify_bound_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (pool :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) =
      Some (operation parameter handle :: rest).
  Hypothesis contract_frame : forall token rest,
    prim "CONTRACT_FA2_TRANSFER" (token :: rest) =
      Some ((match contract_lookup token with None => VNone | Some handle => VSome handle end) :: rest).


  Variable decode_call : value -> option (value * value).
  Hypothesis operation_fields : forall parameter target,
    decode_call (operation parameter target) = Some (target,parameter).
  Hypothesis sender_other : sender <> pool.
  Variable represents : value -> list note -> Prop.
  Hypothesis note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists nextnotes, represents next nextnotes /\ note_transition notes nextnotes balance.
  Hypothesis represented_liability_unique : forall state a b,
    represents state a -> represents state b -> liability a = liability b.

  Lemma pair_entries_injective : forall xs ys,
    FA2PublicSuccess.pair_entries xs = FA2PublicSuccess.pair_entries ys -> xs = ys.
  Proof.
    induction xs as [|[x q] xs IH]; intros [|[y r] ys] H;
      cbn [FA2PublicSuccess.pair_entries map] in H; try discriminate; [reflexivity|].
    inversion H; subst. f_equal. now apply IH.
  Qed.
  Lemma withdrawal_values_as_pairs : forall xs,
    withdrawal_values xs = FA2PublicSuccess.pair_entries (quantity_pairs xs).
  Proof.
    intros. unfold withdrawal_values,FA2PublicSuccess.pair_entries,quantity_pairs.
    rewrite map_map. apply map_ext. intros []; reflexivity.
  Qed.
  Lemma parsed_withdrawal_quantities : forall raw quantities,
    FA2PublicSuccess.pair_entries (rev raw) = withdrawal_values quantities ->
    raw = quantity_pairs (rev quantities).
  Proof.
    intros raw quantities H. rewrite withdrawal_values_as_pairs in H.
    apply pair_entries_injective in H.
    apply (f_equal (@rev (value * value))) in H.
    rewrite rev_involutive, <- quantity_pairs_rev in H. exact H.
  Qed.

  (* The canonical single-SENDER map primitive is the SAME environment used
     by the whole parsed converse. Its actual Octez-map refinement is open. *)
  Theorem whole_parsed_fa2_success_produces_source_certificate :
    forall txs old token id frame output oldnotes,
    run prim 139 SourceLink.parsed_fa2_full
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) = Some output ->
    represents old oldnotes ->
    amount = 0%nat /\ exists final emitted transfers newnotes,
      output = VPair (VList emitted) (VPair final (VPair token id)) :: frame /\
      represents final newnotes /\
      source_entry_certificate eq_value pool oldnotes newnotes emitted transfers /\
      liability newnotes - liability oldnotes <= net_delta eq_value pool transfers /\
      (forall before : ledger, liability oldnotes <= before pool ->
        liability newnotes <= settle eq_value transfers before pool).
  Proof.
    intros txs old token id frame output oldnotes RUN REPR.
    assert (EXTRACT : amount = 0%nat /\ exists final entries withdrawals sum,
      FA2MixedBatch.mixed_trace verify unpack pack sender lookup update txs old
        (VMap []) [] final (VMap entries) (FA2PublicSuccess.pair_entries (rev withdrawals)) /\
      FA2SenderMap.shape sender (VMap entries) /\ FA2SenderMap.amount (VMap entries) = sum /\
      FA2SenderMap.counted_trace sender eq_value verify unpack pack txs old
        (VMap []) [] final (VMap entries) (FA2PublicSuccess.pair_entries (rev withdrawals)) sum /\
      ((entries = [] /\ withdrawals = [] /\
        output = VPair (VList []) (VPair final (VPair token id)) :: frame) \/
       ((List.length entries + List.length withdrawals <> 0)%nat /\ exists handle,
        contract_lookup token = Some handle /\
        output = VPair (VList [operation (VList (FA2PublicSuccess.transfer_groups pool id entries withdrawals)) handle])
          (VPair final (VPair token id)) :: frame))).
    { eapply FA2ParsedInverse.parsed_fa2_success_classifies_output; eauto. }
    destruct EXTRACT as [HA [final [entries [withdrawals [sum [MIXED [SHAPE [SUM [TRACE CASE]]]]]]]]].
    split; [exact HA|].
    destruct (fa2_source_public_movements_cover_liability_change eq_value verify unpack pack
      pool sender id sender_other represents note_soundness txs old final
      (VMap entries) (FA2PublicSuccess.pair_entries (rev withdrawals)) sum oldnotes TRACE REPR)
      as [ns [deposits [quantities [HR [HMAP [HWS [HD HMARGIN]]]]]]].
    assert (ENTRIES : entries = quantity_pairs deposits) by congruence.
    pose proof (parsed_withdrawal_quantities _ _ HWS) as WITHDRAWALS.
    destruct CASE as [[HE [HW OUTPUT]]|[HNONEMPTY [handle [LOOKUP OUTPUT]]]].
    - subst entries withdrawals.
      assert (CERT : source_entry_certificate eq_value pool oldnotes ns [] []).
      { eapply (fa2_private_source_entry eq_value pool oldnotes ns [] []
          verify unpack pack sender id represents txs old final sum); eauto. }
      pose proof (source_entry_covers_new_note_liability _ _ _ _ _ _ CERT) as BOUND.
      exists final,[],[],ns. split; [exact OUTPUT|]. split; [exact HR|].
      split; [exact CERT|]. split; [exact BOUND|].
      intros before BACKED. rewrite settlement_reserve_effect. cbn [net_delta] in *. lia.
    - rewrite ENTRIES,WITHDRAWALS in OUTPUT.
      let emitted := constr:([operation (VList (FA2PublicSuccess.transfer_groups pool id
        (quantity_pairs deposits) (quantity_pairs (rev quantities)))) handle]) in
      let transfers := constr:(deposit_movements pool deposits ++ movements pool (rev quantities)) in
      assert (DECODE : decode_fa2_operations eq_value id handle decode_call emitted = Some transfers).
      { apply (decode_fa2_constructed_singleton eq_value id handle decode_call operation operation_fields).
        apply fa2_public_parameter_decodes_exact_movements. }
      assert (CERT : source_entry_certificate eq_value pool oldnotes ns
        [operation (VList (FA2PublicSuccess.transfer_groups pool id
          (quantity_pairs deposits) (quantity_pairs (rev quantities)))) handle]
        (deposit_movements pool deposits ++ movements pool (rev quantities))).
      { eapply fa2_source_entry with (verify:=verify) (unpack:=unpack)
          (pack:=pack) (sender:=sender) (token_id:=id) (represents:=represents)
          (txs:=txs) (initial:=old) (final:=final) (sum:=sum); eauto. }
      pose proof (source_entry_covers_new_note_liability _ _ _ _ _ _ CERT) as BOUND.
      exists final,
        [operation (VList (FA2PublicSuccess.transfer_groups pool id
          (quantity_pairs deposits) (quantity_pairs (rev quantities)))) handle],
        (deposit_movements pool deposits ++ movements pool (rev quantities)),ns.
      split; [exact OUTPUT|]. split; [exact HR|].
      split; [exact CERT|]. split; [exact BOUND|].
      intros before BACKED. rewrite settlement_reserve_effect. lia.
  Qed.
End ParsedCollateral.
Print Assumptions whole_parsed_fa2_success_produces_source_certificate.
