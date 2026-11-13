(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketPrimitives TicketInit TicketCompleteSuccess TicketMixedBatch
  TicketLoopBody TicketFinal TicketInitInverse TicketStepInverse TicketPostInverse.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Success of the whole modeled source program implies its guards, a valid
   trace, zero final received credit, exact output and quantity conservation.
   Input slots are arbitrary optional typed-shape tickets: their configured
   identities are DERIVED. Protocol typing/linearity, encoding, crypto and
   operation execution/refinement remain external obligations. *)
Section Whole.
  Variable prim : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack handle : value -> option value.
  Variable operation : value -> value -> value.
  Variable compare_value : value -> value -> Z.
  Variable amount : nat.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez amount :: rest).
  Hypothesis compare_frame : forall left right rest,
    prim "COMPARE_identity" (left :: right :: rest) = Some (VInt (compare_value left right) :: rest).
  Hypothesis compare_zero : forall left right, compare_value left right = 0 <-> left = right.
  Hypothesis join_same : forall issuer contents left right rest,
    prim "JOIN_ticket" (VPair (VTicket issuer contents left) (VTicket issuer contents right) :: rest) =
    Some (VSome (VTicket issuer contents (left + right)) :: rest).
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
  Theorem successful_whole_call_extracts_identity_trace_zero_credit_and_accounting :
    forall old paid issuer contents txs state frame output,
    run prim 150 TicketCompleteSuccess.full_code
      (VPair (VPair (TicketInitInverse.slot_value paid) (VList txs))
        (VPair state (VPair (TicketInitInverse.slot_value old) (VPair issuer contents))) :: frame) = Some output ->
    amount = 0%nat /\
    exists oldq paidq final finalslot finalops total,
      TicketInitInverse.slot_value old = TicketInit.held_value issuer contents oldq /\
      TicketInitInverse.slot_value paid = TicketInit.held_value issuer contents paidq /\
      TicketMixedBatch.ticket_trace verify unpack handle operation issuer contents txs state
        (TicketInit.held_value issuer contents (TicketInit.joined_slot oldq paidq))
        (TicketInit.incoming_credit paidq) [] final
        (TicketInit.held_value issuer contents finalslot) 0 finalops total /\
      output = VPair (VList (rev finalops))
        (VPair final (VPair (TicketInit.held_value issuer contents finalslot) (VPair issuer contents))) :: frame /\
      (Z.of_nat (TicketInit.slot_quantity oldq) - total = Z.of_nat (TicketInit.slot_quantity finalslot))%Z.
  Proof.
    intros old paid issuer contents txs state frame output H.
    unfold TicketCompleteSuccess.full_code in H.
    assert (INIT : amount = 0%nat /\ exists oldq paidq,
      TicketInitInverse.slot_value old = TicketInit.held_value issuer contents oldq /\
      TicketInitInverse.slot_value paid = TicketInit.held_value issuer contents paidq /\
      run prim 138 (Iter ticket_iteration :: TicketFinal.final_code)
        (VList txs :: state :: TicketInit.held_value issuer contents (TicketInit.joined_slot oldq paidq) ::
         VNat (TicketInit.incoming_credit paidq) :: VPair issuer contents :: VList [] :: frame) = Some output).
    { eapply TicketInitInverse.successful_initialization_extracts_identity_and_tail; eauto. }
    destruct INIT as [HA [oldq [paidq [HO [HP HR]]]]]. split; [exact HA|].
    assert (POST : exists final finalslot finalops total,
      ticket_trace verify unpack handle operation issuer contents txs state
        (TicketInit.held_value issuer contents (TicketInit.joined_slot oldq paidq))
        (TicketInit.incoming_credit paidq) [] final
        (TicketInit.held_value issuer contents finalslot) 0 finalops total /\
      output = VPair (VList (rev finalops))
        (VPair final (VPair (TicketInit.held_value issuer contents finalslot) (VPair issuer contents))) :: frame /\
      (Z.of_nat (TicketInit.slot_quantity (TicketInit.joined_slot oldq paidq)) -
       Z.of_nat (TicketInit.incoming_credit paidq) - total = Z.of_nat (TicketInit.slot_quantity finalslot))%Z).
    { eapply TicketPostInverse.successful_batch_extracts_trace_and_zero_credit; eauto. }
    destruct POST as [final [finalslot [finalops [total [HT [HOUT HQ]]]]]].
    exists oldq, paidq, final, finalslot, finalops, total.
    split; [exact HO|]. split; [exact HP|]. split; [exact HT|]. split; [exact HOUT|].
    rewrite TicketInit.joined_quantity_is_old_plus_received, Nat2Z.inj_add in HQ. lia.
  Qed.
End Whole.
Print Assumptions successful_whole_call_extracts_identity_trace_zero_credit_and_accounting.
