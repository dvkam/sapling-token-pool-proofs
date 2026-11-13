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
Require Import SourceLink TicketFullInverse.
Section ParsedWhole.
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
  Theorem parsed_success_extracts_identity_trace_zero_credit_and_accounting :
    forall old paid issuer contents txs state frame output,
    run prim 150 (SourceLink.parsed_ticket_init ++ Iter SourceLink.parsed_ticket_iteration :: SourceLink.parsed_ticket_final)
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
    rewrite SourceLink.ticket_full_matches in H.
    eapply TicketFullInverse.successful_whole_call_extracts_identity_trace_zero_credit_and_accounting; eauto.
  Qed.
End ParsedWhole.
Print Assumptions parsed_success_extracts_identity_trace_zero_credit_and_accounting.
