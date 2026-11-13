(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketPrimitives TicketWithdrawal TicketLoopBody TicketMixedBatch TicketInit.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

Inductive ticket_step_event
  (verify : value -> value -> option (value * Z * value))
  (unpack handle : value -> option value) (operation : value -> value -> value)
  (issuer contents : value) :
  value -> value -> option nat -> nat -> list value ->
  value -> option nat -> nat -> list value -> Z -> Prop :=
| event_partial : forall tx old quantity credit ops bytes balance next recipient receiver,
    verify tx old = Some (bytes,balance,next) -> 0 < balance ->
    (Z.to_nat balance < quantity)%nat -> unpack bytes = Some recipient -> handle recipient = Some receiver ->
    ticket_step_event verify unpack handle operation issuer contents tx old (Some quantity) credit ops
      next (Some (quantity - Z.to_nat balance)%nat) credit
      (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) balance
| event_full : forall tx old credit ops bytes balance next recipient receiver,
    verify tx old = Some (bytes,balance,next) -> 0 < balance ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    ticket_step_event verify unpack handle operation issuer contents tx old (Some (Z.to_nat balance)) credit ops
      next None credit (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) balance
| event_nonpositive : forall tx old slot credit ops balance next,
    verify tx old = Some (VBytes [],balance,next) -> balance <= 0 ->
    (Z.to_nat (Z.abs balance) <= credit)%nat ->
    ticket_step_event verify unpack handle operation issuer contents tx old slot credit ops
      next slot (credit - Z.to_nat (Z.abs balance))%nat ops balance.

Section Inverse.
  Variable prim : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack handle : value -> option value.
  Variable operation : value -> value -> value.
  Variable issuer contents : value.
  Hypothesis verify_some : forall tx old bound balance next rest,
    verify tx old = Some (bound,balance,next) ->
    prim "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) = Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis verify_none : forall tx old rest, verify tx old = None ->
    prim "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) = Some (VNone :: rest).
  Hypothesis verify_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.
  Hypothesis unpack_some : forall bytes recipient rest, unpack bytes = Some recipient ->
    prim "UNPACK_address" (bytes :: rest) = Some (VSome recipient :: rest).
  Hypothesis unpack_none : forall bytes rest, unpack bytes = None ->
    prim "UNPACK_address" (bytes :: rest) = Some (VNone :: rest).
  Hypothesis handle_some : forall recipient receiver rest, handle recipient = Some receiver ->
    prim "CONTRACT_ticket" (recipient :: rest) = Some (VSome receiver :: rest).
  Hypothesis handle_none : forall recipient rest, handle recipient = None ->
    prim "CONTRACT_ticket" (recipient :: rest) = Some (VNone :: rest).
  Hypothesis split_frame : forall issuer0 contents0 quantity left right rest,
    prim "SPLIT_ticket" (VTicket issuer0 contents0 quantity :: VPair (VNat left) (VNat right) :: rest) =
    Some (split_ticket (VTicket issuer0 contents0 quantity) left right :: rest).
  Hypothesis transfer_frame : forall ticket receiver rest,
    prim "TRANSFER_ticket" (ticket :: VMutez 0 :: receiver :: rest) = Some (operation ticket receiver :: rest).

  Lemma failed_verify_tail : forall fuel rest,
    run prim (4 + fuel)%nat (tl ticket_iteration) (VNone :: rest) = None.
  Proof. reflexivity. Qed.
  Lemma unpack_any_slot : forall fuel amount bound state held credit asset ops frame,
    run prim (2 + fuel)%nat ticket_withdrawal
      (VNat amount :: bound :: state :: held :: credit :: asset :: VList ops :: frame) =
    match prim "UNPACK_address" (bound :: VNat amount :: state :: held :: credit :: asset :: VList ops :: frame) with
    | Some s => run prim fuel ticket_unpack_tail s | None => None end.
  Proof. reflexivity. Qed.
  Lemma contract_any_slot : forall fuel amount recipient state held credit asset ops frame,
    run prim (2 + fuel)%nat ticket_unpack_tail
      (VSome recipient :: VNat amount :: state :: held :: credit :: asset :: VList ops :: frame) =
    match prim "CONTRACT_ticket" (recipient :: VNat amount :: state :: held :: credit :: asset :: VList ops :: frame) with
    | Some s => run prim fuel ticket_contract_tail s | None => None end.
  Proof. reflexivity. Qed.
  Lemma unpack_reject : forall fuel rest,
    run prim (4 + fuel)%nat ticket_unpack_tail (VNone :: rest) = None.
  Proof. reflexivity. Qed.
  Lemma contract_reject : forall fuel rest,
    run prim (4 + fuel)%nat ticket_contract_tail (VNone :: rest) = None.
  Proof. reflexivity. Qed.
  Lemma held_none_reject : forall fuel amount receiver state credit asset ops frame,
    run prim (7 + fuel)%nat ticket_contract_tail
      (VSome receiver :: VNat amount :: state :: VNone :: credit :: asset :: VList ops :: frame) = None.
  Proof. reflexivity. Qed.
  Lemma nonempty_bound_reject : forall fuel byte bytes state held remaining asset ops frame,
    run prim (8 + fuel)%nat ticket_empty_bound_guard
      (VBytes (byte :: bytes) :: state :: held :: VNat remaining :: asset :: VList ops :: frame) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.

  Lemma positive_needs_unpack : forall amount bound state held credit asset ops frame result,
    run prim 128 ticket_withdrawal
      (VNat amount :: bound :: state :: held :: credit :: asset :: VList ops :: frame) = Some result ->
    exists recipient receiver, unpack bound = Some recipient /\ handle recipient = Some receiver /\ held <> VNone.
  Proof.
    intros amount bound state held credit asset ops frame result H.
    rewrite (unpack_any_slot 126) in H.
    destruct (unpack bound) as [recipient|] eqn:HU.
    2: { rewrite (unpack_none bound) in H by exact HU. rewrite (unpack_reject 122) in H. discriminate. }
    rewrite (unpack_some bound recipient) in H by exact HU.
    rewrite (contract_any_slot 124) in H.
    destruct (handle recipient) as [receiver|] eqn:HC.
    2: { rewrite (handle_none recipient) in H by exact HC. rewrite (contract_reject 120) in H. discriminate. }
    rewrite (handle_some recipient receiver) in H by exact HC.
    exists recipient, receiver. split; [reflexivity|]. split; [exact HC|].
    intro HE. subst held. rewrite (held_none_reject 117) in H. discriminate.
  Qed.

  Lemma nonpositive_needs_credit_and_empty_bound : forall amount bytes state held credit asset ops frame result,
    run prim 128 TicketLoopBody.ticket_nonpositive
      (VNat amount :: VBytes bytes :: state :: held :: VNat credit :: asset :: VList ops :: frame) = Some result ->
    (amount <= credit)%nat /\ bytes = [].
  Proof.
    intros amount bytes state held credit asset ops frame result H.
    destruct (le_dec amount credit) as [HA|HA].
    - split; [exact HA|].
      rewrite (ticket_credit_step prim 125) in H. cbv zeta in H.
      assert (HR : Z.of_nat credit - Z.of_nat amount = Z.of_nat (credit - amount)) by (rewrite Nat2Z.inj_sub; lia).
      assert (HN : Z.ltb (Z.of_nat (credit - amount)) 0 = false) by (apply Z.ltb_ge; lia).
      rewrite HR, HN, Nat2Z.id, (ticket_credit_ready_step prim 122) in H.
      destruct bytes as [|byte bytes]; [reflexivity|].
      rewrite (nonempty_bound_reject 115) in H. discriminate.
    - rewrite (ticket_credit_step prim 125) in H. cbv zeta in H.
      assert (HN : Z.ltb (Z.of_nat credit - Z.of_nat amount) 0 = true) by (apply Z.ltb_lt; lia).
      rewrite HN, (ticket_credit_failure_step prim 121) in H. discriminate.
  Qed.

  Theorem successful_step_extracts_event : forall tx old slot credit ops asset frame result,
    run prim 137 ticket_iteration
      (tx :: old :: TicketInit.held_value issuer contents slot :: VNat credit :: asset :: VList ops :: frame) = Some result ->
    exists next nextslot nextcredit nextops balance,
      result = next :: TicketInit.held_value issuer contents nextslot :: VNat nextcredit :: asset :: VList nextops :: frame /\
      ticket_step_event verify unpack handle operation issuer contents tx old slot credit ops
        next nextslot nextcredit nextops balance.
  Proof.
    intros tx old slot credit ops asset frame result Hrun.
    destruct (verify tx old) as [[[bound balance] next]|] eqn:HV.
    2: { rewrite (ticket_verify_step prim 136), (verify_none tx old) in Hrun by exact HV.
         rewrite (failed_verify_tail 132) in Hrun. discriminate. }
    destruct (verify_bytes tx old bound balance next HV) as [bytes HE]. subst bound.
    destruct (Z_lt_dec 0 balance) as [HP|HN].
    - assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; exact HP).
      assert (HA : Z.to_nat (Z.abs balance) = Z.to_nat balance) by (rewrite Z.abs_eq; lia).
      pose proof Hrun as HB.
      rewrite (ticket_verify_step prim 136), (verify_some tx old (VBytes bytes) balance next) in HB by exact HV.
      rewrite (ticket_numeric_step prim 127), HG, HA in HB.
      destruct (run prim 128 ticket_withdrawal
        (VNat (Z.to_nat balance) :: VBytes bytes :: next :: TicketInit.held_value issuer contents slot ::
         VNat credit :: asset :: VList ops :: frame)) as [branch|] eqn:HW; [|discriminate].
      destruct (positive_needs_unpack _ _ _ _ _ _ _ _ _ HW) as [recipient [receiver [HU [HC HS]]]].
      destruct slot as [quantity|]; [|contradiction].
      cbn [TicketInit.held_value] in HW, Hrun, HS.
      destruct (Nat.lt_trichotomy quantity (Z.to_nat balance)) as [HL|[HEq|HGt]].
      + assert (BAD : run prim 128 ticket_withdrawal
          (VNat (Z.to_nat balance) :: VBytes bytes :: next :: VSome (VTicket issuer contents quantity) ::
           VNat credit :: asset :: VList ops :: frame) = None).
        { eapply ticket_withdrawal_insufficient; eauto. }
        rewrite BAD in HW. discriminate.
      + subst quantity.
        assert (STEP : run prim 137 ticket_iteration
          (tx :: old :: VSome (VTicket issuer contents (Z.to_nat balance)) :: VNat credit :: asset :: VList ops :: frame) =
          Some (next :: VNone :: VNat credit :: asset ::
            VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame)).
        { eapply verified_ticket_full_withdrawal_iteration; eauto. }
        rewrite STEP in Hrun. inversion Hrun; subst result.
        exists next, None, credit, (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops), balance.
        split; [reflexivity|]. eapply event_full; eauto.
      + assert (STEP : run prim 137 ticket_iteration
          (tx :: old :: VSome (VTicket issuer contents quantity) :: VNat credit :: asset :: VList ops :: frame) =
          Some (next :: VSome (VTicket issuer contents (quantity - Z.to_nat balance)) :: VNat credit :: asset ::
            VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame)).
        { eapply verified_ticket_partial_withdrawal_iteration; eauto. }
        rewrite STEP in Hrun. inversion Hrun; subst result.
        exists next, (Some (quantity - Z.to_nat balance)%nat), credit,
          (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops), balance.
        split; [reflexivity|]. eapply event_partial; eauto.
    - assert (HG : Z.gtb balance 0 = false).
      { apply Bool.not_true_is_false. intro HG. apply Z.gtb_lt in HG. lia. }
      pose proof Hrun as HB.
      rewrite (ticket_verify_step prim 136), (verify_some tx old (VBytes bytes) balance next) in HB by exact HV.
      rewrite (ticket_numeric_step prim 127), HG in HB.
      destruct (run prim 128 TicketLoopBody.ticket_nonpositive
        (VNat (Z.to_nat (Z.abs balance)) :: VBytes bytes :: next :: TicketInit.held_value issuer contents slot ::
         VNat credit :: asset :: VList ops :: frame)) as [branch|] eqn:HW; [|discriminate].
      destruct (nonpositive_needs_credit_and_empty_bound _ _ _ _ _ _ _ _ _ HW) as [HA HE]. subst bytes.
      assert (STEP : run prim 137 ticket_iteration
        (tx :: old :: TicketInit.held_value issuer contents slot :: VNat credit :: asset :: VList ops :: frame) =
        Some (next :: TicketInit.held_value issuer contents slot :: VNat (credit - Z.to_nat (Z.abs balance)) :: asset :: VList ops :: frame)).
      { eapply verified_ticket_nonpositive_iteration; eauto; lia. }
      rewrite STEP in Hrun. inversion Hrun; subst result.
      exists next, slot, (credit - Z.to_nat (Z.abs balance))%nat, ops, balance.
      split; [reflexivity|]. eapply event_nonpositive; eauto; lia.
  Qed.

  Theorem successful_loop_extracts_trace : forall txs old slot credit ops asset frame result,
    iterate (fun tx s => run prim 137 ticket_iteration (tx :: s)) txs
      (old :: TicketInit.held_value issuer contents slot :: VNat credit :: asset :: VList ops :: frame) = Some result ->
    exists final finalslot finalcredit finalops total,
      result = final :: TicketInit.held_value issuer contents finalslot :: VNat finalcredit :: asset :: VList finalops :: frame /\
      TicketMixedBatch.ticket_trace verify unpack handle operation issuer contents txs old
        (TicketInit.held_value issuer contents slot) credit ops final
        (TicketInit.held_value issuer contents finalslot) finalcredit finalops total.
  Proof.
    induction txs as [|tx txs IH]; intros old slot credit ops asset frame result H.
    - cbn [iterate] in H. inversion H; subst result.
      exists old, slot, credit, ops, 0. split; [reflexivity|constructor].
    - cbn [iterate] in H.
      destruct (run prim 137 ticket_iteration
        (tx :: old :: TicketInit.held_value issuer contents slot :: VNat credit :: asset :: VList ops :: frame))
        as [step|] eqn:HS; [|discriminate].
      destruct (successful_step_extracts_event tx old slot credit ops asset frame step HS)
        as [next [nextslot [nextcredit [nextops [balance [ES HE]]]]]]. subst step.
      destruct (IH next nextslot nextcredit nextops asset frame result H)
        as [final [finalslot [finalcredit [finalops [total [ER HT]]]]]].
      exists final, finalslot, finalcredit, finalops, (balance + total). split; [exact ER|].
      inversion HE; subst; cbn [TicketInit.held_value] in *.
      + eapply TicketMixedBatch.ticket_partial; eauto.
      + eapply TicketMixedBatch.ticket_full; eauto.
      + eapply TicketMixedBatch.ticket_nonpositive; eauto.
  Qed.
End Inverse.
Print Assumptions successful_step_extracts_event.
Print Assumptions successful_loop_extracts_trace.
