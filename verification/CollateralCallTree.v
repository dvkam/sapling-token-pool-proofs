(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA12MixedBatch FA2SenderMap FA2PublicSuccess
  AssetLedger SaplingNotes PoolCollateral
  InternalQueue ManagerBatch.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Section SourceCertificates.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable pool : value.

  (* Certificates contain actual source traces and witness/representation
     facts, NOT a collateral inequality or an invariant-preservation premise.
     A protocol refinement must produce them from actual pool execution. *)
  Inductive source_entry_certificate (oldnotes newnotes : list note)
    (raw_emitted : list value) (transfers : list transfer) : Prop :=
  | fa12_source_entry :
      forall verify unpack pack sender handle operation decode_call represents
        txs initial final ds ws,
      (forall parameter target, decode_call (operation parameter target) = Some (target,parameter)) ->
      sender <> pool ->
      (forall tx old bound balance next ns,
        verify tx old = Some (bound,balance,next) -> represents old ns ->
        exists nextnotes, represents next nextnotes /\ note_transition ns nextnotes balance) ->
      mixed_trace verify unpack pack pool sender handle operation txs initial [] [] final ds ws ->
      represents initial oldnotes -> represents final newnotes ->
      (forall a b, represents final a -> represents final b -> liability a = liability b) ->
      raw_emitted = rev ds ++ rev ws ->
      decode_fa12_operations eq_value decode_call handle raw_emitted = Some transfers ->
      source_entry_certificate oldnotes newnotes raw_emitted transfers
  | fa2_source_entry :
      forall verify unpack pack sender token_id (operation : value -> value -> value)
        (handle : value) decode_call represents
        txs initial final fm fws sum deposits withdrawals,
      (forall parameter target, decode_call (operation parameter target) = Some (target,parameter)) ->
      sender <> pool ->
      (forall tx old bound balance next ns,
        verify tx old = Some (bound,balance,next) -> represents old ns ->
        exists nextnotes, represents next nextnotes /\ note_transition ns nextnotes balance) ->
      FA2SenderMap.counted_trace sender eq_value verify unpack pack
        txs initial (VMap []) [] final fm fws sum ->
      represents initial oldnotes -> represents final newnotes ->
      (forall a b, represents final a -> represents final b -> liability a = liability b) ->
      fm = VMap (quantity_pairs deposits) -> fws = withdrawal_values withdrawals ->
      raw_emitted = [operation
        (VList (FA2PublicSuccess.transfer_groups pool token_id
          (quantity_pairs deposits) (quantity_pairs (rev withdrawals)))) handle] ->
      transfers = deposit_movements pool deposits ++ movements pool (rev withdrawals) ->
      decode_fa2_operations eq_value token_id handle decode_call raw_emitted = Some transfers ->
      source_entry_certificate oldnotes newnotes raw_emitted transfers
  | fa2_private_source_entry :
      forall verify unpack pack sender (token_id : value) represents txs initial final sum,
      sender <> pool ->
      (forall tx old bound balance next ns,
        verify tx old = Some (bound,balance,next) -> represents old ns ->
        exists nextnotes, represents next nextnotes /\ note_transition ns nextnotes balance) ->
      FA2SenderMap.counted_trace sender eq_value verify unpack pack
        txs initial (VMap []) [] final (VMap []) [] sum ->
      represents initial oldnotes -> represents final newnotes ->
      (forall a b, represents final a -> represents final b -> liability a = liability b) ->
      raw_emitted = [] -> transfers = [] ->
      source_entry_certificate oldnotes newnotes raw_emitted transfers.

  Theorem source_entry_covers_new_note_liability : forall oldnotes newnotes emitted transfers,
    source_entry_certificate oldnotes newnotes emitted transfers ->
    liability newnotes - liability oldnotes <= net_delta eq_value pool transfers.
  Proof.
    intros oldnotes newnotes emitted transfers HC. destruct HC.
    - destruct (fa12_emitted_operations_cover_liability_change eq_value verify unpack pack
        pool sender handle operation decode_call H H0 represents H1
        txs initial final ds ws oldnotes H2 H3) as [fn [ts [HN [HD HM]]]].
      rewrite <- H6, H7 in HD. inversion HD; subst ts.
      pose proof (H5 _ _ H4 HN). lia.
    - subst transfers.
      pose proof (fa2_explicit_source_movements_cover_liability_change eq_value
        verify unpack pack pool sender token_id H0 represents H1
        txs initial final fm fws sum oldnotes newnotes deposits withdrawals
        H2 H3 H4 H5 H6 H7). lia.
    - subst transfers. pose proof (fa2_explicit_source_movements_cover_liability_change eq_value
        verify unpack pack pool sender token_id H represents H0
        txs initial final (VMap []) [] sum oldnotes newnotes [] []
        H1 H2 H3 H4 eq_refl eq_refl) as HP.
      change (0 >= liability newnotes - liability oldnotes) in HP.
      change (liability newnotes - liability oldnotes <= 0). lia.
  Qed.
End SourceCertificates.

(* Internal operations retain independent native identity. VM operation
   values are payload erasures; equality of payloads never identifies nonces.
   The protocol bridge must preserve this erasure and each native nonce. *)
Section ConcreteQueue.
  Context {Context Root Internal : Type}.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable pool : value.
  Variable balances : Context -> ledger.
  Variable live_notes : Context -> list note.
  Variable payload : Internal -> value.
  Variable nonce : Internal -> nat.
  Variable apply_internal : Context -> list nat -> Internal -> option (Context * list Internal).
  Variable apply_root : Context -> list nat -> Root -> option (Context * list Internal).
  Variable finish_root : Context -> option Context.
  (* Actual operation decoding/asset identity must justify this projection.
     A token operation can contain many FA2 movements. Pool calls and other
     calls have no immediate asset obligation in this projection. *)
  Variable projected_movements : value -> list transfer.
  Fixpoint pending_movements (ops : list Internal) : list transfer :=
    match ops with [] => [] | op :: rest => projected_movements (payload op) ++ pending_movements rest end.
  Definition pending_margin (c : Context) (ops : list Internal) : Z :=
    balances c pool + net_delta eq_value pool (pending_movements ops) - liability (live_notes c).
  Definition backed (c : Context) := liability (live_notes c) <= balances c pool.
  Definition pending_backed c ops := 0 <= pending_margin c ops.
  Lemma pending_app : forall a b,
    pending_movements (a ++ b) = pending_movements a ++ pending_movements b.
  Proof. induction a; intros; cbn [app pending_movements]; [reflexivity|rewrite IHa, app_assoc; reflexivity]. Qed.

  (* This is an exhaustive refinement obligation on SUCCESSFUL steps.
     Funding/allowance/issuer policy are checked by actual execution before
     these cases apply. A framed call may emit donations, but cannot create
     an unaccounted negative obligation against the pool. The latter follows
     only with the chosen issuer's custody/authorization policy. *)
  Inductive concrete_step (before : Context) (op : Internal) (after : Context)
    (emitted : list Internal) : Prop :=
  | issuer_step :
      (forall account, balances after account =
        settle eq_value (projected_movements (payload op)) (balances before) account) ->
      live_notes after = live_notes before ->
      0 <= net_delta eq_value pool (pending_movements emitted) ->
      concrete_step before op after emitted
  | reentrant_pool_step :
      projected_movements (payload op) = [] ->
      (forall account, balances after account = balances before account) ->
      source_entry_certificate eq_value pool (live_notes before) (live_notes after)
        (map payload emitted) (pending_movements emitted) ->
      concrete_step before op after emitted
  | framed_step :
      projected_movements (payload op) = [] ->
      (forall account, balances after account = balances before account) ->
      live_notes after = live_notes before ->
      0 <= net_delta eq_value pool (pending_movements emitted) ->
      concrete_step before op after emitted.

  Hypothesis every_successful_internal_step_refines : forall before seen op after emitted,
    apply_internal before seen op = Some (after,emitted) -> concrete_step before op after emitted.

  Theorem concrete_step_preserves_pending_margin : forall before op after emitted rest,
    concrete_step before op after emitted ->
    pending_margin before (op :: rest) <= pending_margin after (emitted ++ rest).
  Proof.
    intros before op after emitted rest HS. unfold pending_margin.
    rewrite pending_app, net_delta_app. cbn [pending_movements]. rewrite net_delta_app.
    destruct HS.
    - rewrite H, H0, settlement_reserve_effect. lia.
    - rewrite H, H0. cbn [net_delta].
      pose proof (source_entry_covers_new_note_liability _ _ _ _ _ _ H1). lia.
    - rewrite H,H0,H1. cbn [net_delta]. lia.
  Qed.

  Theorem concrete_internal_queue_ends_backed : forall fuel before seen work result,
    pending_backed before work ->
    run nonce apply_internal fuel before seen work = Some result -> backed (final_context result).
  Proof.
    intros fuel before seen work result HB HR.
    assert (HP : pending_backed (final_context result) []).
    { eapply successful_queue_discharges_pending_invariant; [|exact HB|exact HR].
      intros c seen0 op rest next emitted HI HF HS.
      unfold pending_backed in *.
      pose proof (concrete_step_preserves_pending_margin _ _ _ _ rest
        (every_successful_internal_step_refines _ _ _ _ _ HS)). lia. }
    unfold pending_backed,pending_margin in HP. cbn [pending_movements net_delta] in HP.
    unfold backed. lia.
  Qed.

  (* Root classifications also forbid unauthorized independent debits of
     pool custody. For a direct issuer root, nonnegative net movement must
     be derived from issuer authorization (e.g. no approved pool operator).
     No storage/ledger backing predicate is assumed by these constructors. *)
  Inductive concrete_root_step (before after : Context) (emitted : list Internal) : Prop :=
  | root_pool_step :
      (forall account, balances after account = balances before account) ->
      source_entry_certificate eq_value pool (live_notes before) (live_notes after)
        (map payload emitted) (pending_movements emitted) -> concrete_root_step before after emitted
  | root_framed_step :
      live_notes after = live_notes before ->
      0 <= balances after pool - balances before pool ->
      0 <= net_delta eq_value pool (pending_movements emitted) ->
      concrete_root_step before after emitted.
  Hypothesis every_successful_root_refines : forall before seen root after emitted,
    apply_root before seen root = Some (after,emitted) -> concrete_root_step before after emitted.
  Hypothesis finish_frames_asset_and_notes : forall before after,
    finish_root before = Some after -> balances after pool = balances before pool /\
      live_notes after = live_notes before.

  Theorem concrete_committed_manager_batch_is_backed : forall roots fuel before seen result,
    backed before ->
    run_batch nonce apply_internal apply_root finish_root roots fuel before seen = Some result ->
    backed (final_context result).
  Proof.
    intros roots fuel before seen result HB HR.
    assert (HP : pending_backed (final_context result) []).
    { eapply successful_batch_settles_every_root; [| | | |exact HR].
      - intros c seen0 root next emitted HI HS.
        destruct (every_successful_root_refines _ _ _ _ _ HS).
        + pose proof (source_entry_covers_new_note_liability _ _ _ _ _ _ H0).
          unfold pending_backed,pending_margin in *. cbn [pending_movements net_delta] in HI.
          rewrite H. lia.
        + unfold pending_backed,pending_margin in *. cbn [pending_movements net_delta] in HI.
          rewrite H. lia.
      - intros c seen0 op rest next emitted HI HF HS.
        unfold pending_backed in *.
        pose proof (concrete_step_preserves_pending_margin _ _ _ _ rest
          (every_successful_internal_step_refines _ _ _ _ _ HS)). lia.
      - intros c next HI HS. destruct (finish_frames_asset_and_notes _ _ HS) as [HL HN].
        unfold pending_backed,pending_margin in *. now rewrite HL,HN.
      - unfold pending_backed,pending_margin,backed in *. cbn [pending_movements net_delta]. lia. }
    unfold pending_backed,pending_margin in HP. cbn [pending_movements net_delta] in HP.
    unfold backed. lia.
  Qed.
End ConcreteQueue.
Print Assumptions source_entry_covers_new_note_liability.
Print Assumptions concrete_internal_queue_ends_backed.
Print Assumptions concrete_committed_manager_batch_is_backed.
