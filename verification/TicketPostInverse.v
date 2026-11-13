(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketPrimitives TicketLoopBody TicketMixedBatch TicketInit TicketFinal TicketPostBatch TicketStepInverse.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

Section Final.
  Variable prim : string -> stack -> option stack.
  Local Opaque run.
  Theorem successful_final_requires_zero_credit : forall state held credit asset ops frame output,
    run prim 137 TicketFinal.final_code (state :: held :: VNat credit :: asset :: VList ops :: frame) = Some output ->
    credit = 0%nat /\ output = VPair (VList (rev ops)) (VPair state (VPair held asset)) :: frame.
  Proof.
    intros state held credit asset ops frame output H.
    destruct credit as [|n].
    - split; [reflexivity|]. rewrite (TicketFinal.zero_credit_returns_at_fuel prim 97) in H.
      inversion H; reflexivity.
    - rewrite (TicketFinal.credit_check_step prim 134) in H.
      assert (HE : Z.eqb (Z.of_nat (S n)) 0 = false) by (apply Z.eqb_neq; lia).
      rewrite HE, (TicketFinal.false_credit_check prim 130) in H. discriminate.
  Qed.
End Final.

Section Batch.
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

  Local Opaque run.
  Theorem successful_batch_extracts_trace_and_zero_credit :
    forall txs old slot credit ops asset frame output,
    run prim 138 (Iter ticket_iteration :: TicketFinal.final_code)
      (VList txs :: old :: TicketInit.held_value issuer contents slot :: VNat credit :: asset :: VList ops :: frame) = Some output ->
    exists final finalslot finalops total,
      TicketMixedBatch.ticket_trace verify unpack handle operation issuer contents txs old
        (TicketInit.held_value issuer contents slot) credit ops final
        (TicketInit.held_value issuer contents finalslot) 0 finalops total /\
      output = VPair (VList (rev finalops)) (VPair final (VPair (TicketInit.held_value issuer contents finalslot) asset)) :: frame /\
      (Z.of_nat (TicketInit.slot_quantity slot) - Z.of_nat credit - total =
       Z.of_nat (TicketInit.slot_quantity finalslot))%Z.
  Proof.
    intros txs old slot credit ops asset frame output H.
    rewrite (TicketPostBatch.loop_then_final_step prim 136) in H.
    destruct (iterate (fun tx s => run prim 137 ticket_iteration (tx :: s)) txs
      (old :: TicketInit.held_value issuer contents slot :: VNat credit :: asset :: VList ops :: frame))
      as [middle|] eqn:HI; [|discriminate].
    assert (EX : exists final finalslot finalcredit finalops total,
      middle = final :: TicketInit.held_value issuer contents finalslot :: VNat finalcredit :: asset :: VList finalops :: frame /\
      ticket_trace verify unpack handle operation issuer contents txs old
        (TicketInit.held_value issuer contents slot) credit ops final
        (TicketInit.held_value issuer contents finalslot) finalcredit finalops total).
    { eapply TicketStepInverse.successful_loop_extracts_trace; eauto. }
    destruct EX as [final [finalslot [finalcredit [finalops [total [EM HT]]]]]]. subst middle.
    destruct (successful_final_requires_zero_credit prim _ _ _ _ _ _ _ H) as [HC HO]. subst finalcredit.
    exists final, finalslot, finalops, total. split; [exact HT|]. split; [exact HO|].
    pose proof (TicketMixedBatch.ticket_trace_credit_adjusted_conservation verify unpack handle operation
      issuer contents txs old (TicketInit.held_value issuer contents slot) credit ops final
      (TicketInit.held_value issuer contents finalslot) 0 finalops total HT) as HQ.
    assert (SLOT : forall s, held_quantity (TicketInit.held_value issuer contents s) = TicketInit.slot_quantity s).
    { intros [q|]; reflexivity. }
    rewrite !SLOT in HQ. simpl in HQ. lia.
  Qed.
End Batch.
Print Assumptions successful_final_requires_zero_credit.
Print Assumptions successful_batch_extracts_trace_and_zero_credit.
