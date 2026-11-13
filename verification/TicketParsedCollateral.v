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
Require Import AssetLedger SaplingNotes PoolCollateral TicketParsedInverse.
Section ParsedCollateral.
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

  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable pool : value.
  Variable represents : value -> list note -> Prop.
  Hypothesis note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists nextnotes, represents next nextnotes /\ note_transition notes nextnotes balance.

  Lemma canonical_held_quantity : forall issuer contents slot,
    held_quantity (TicketInit.held_value issuer contents slot) = TicketInit.slot_quantity slot.
  Proof. intros issuer contents []; reflexivity. Qed.

  (* This says precisely that a returned stored ticket denotes a matching
     pool-owned fragment. It does not mention liability/backing. A native
     ownership/linearity bridge must establish it, including positive ticket
     quantities. The VM's Some 0 extension is not native ticket creation. *)
  Definition returned_slot_owned (issuer contents : value) (slot : option nat)
    (inventory : list owned_fragment) : Prop :=
    forall q, slot = Some q -> exists fragment,
      In fragment inventory /\ owner fragment = pool /\ ticketer fragment = issuer /\
      payload fragment = contents /\ quantity fragment = q.

  Theorem whole_parsed_ticket_success_produces_stored_and_owned_backing :
    forall old paid issuer contents txs state frame output oldnotes,
    run prim 150 (SourceLink.parsed_ticket_init ++
      Iter SourceLink.parsed_ticket_iteration :: SourceLink.parsed_ticket_final)
      (VPair (VPair (TicketInitInverse.slot_value paid) (VList txs))
        (VPair state (VPair (TicketInitInverse.slot_value old) (VPair issuer contents))) :: frame) = Some output ->
    represents state oldnotes ->
    liability oldnotes <= Z.of_nat (held_quantity (TicketInitInverse.slot_value old)) ->
    amount = 0%nat /\ exists oldq paidq final finalslot emitted newnotes,
      TicketInitInverse.slot_value old = TicketInit.held_value issuer contents oldq /\
      TicketInitInverse.slot_value paid = TicketInit.held_value issuer contents paidq /\
      output = VPair (VList emitted)
        (VPair final (VPair (TicketInit.held_value issuer contents finalslot) (VPair issuer contents))) :: frame /\
      represents final newnotes /\
      liability newnotes <= Z.of_nat (TicketInit.slot_quantity finalslot) /\
      (forall inventory, valid_inventory inventory -> returned_slot_owned issuer contents finalslot inventory ->
        liability newnotes <= owned_reserve eq_value pool issuer contents inventory).
  Proof.
    intros old paid issuer contents txs state frame output oldnotes RUN REPR INITIAL.
    assert (EXTRACT : amount = 0%nat /\ exists oldq paidq final finalslot finalops total,
      TicketInitInverse.slot_value old = TicketInit.held_value issuer contents oldq /\
      TicketInitInverse.slot_value paid = TicketInit.held_value issuer contents paidq /\
      TicketMixedBatch.ticket_trace verify unpack handle operation issuer contents txs state
        (TicketInit.held_value issuer contents (TicketInit.joined_slot oldq paidq))
        (TicketInit.incoming_credit paidq) [] final
        (TicketInit.held_value issuer contents finalslot) 0 finalops total /\
      output = VPair (VList (rev finalops))
        (VPair final (VPair (TicketInit.held_value issuer contents finalslot) (VPair issuer contents))) :: frame /\
      Z.of_nat (TicketInit.slot_quantity oldq) - total = Z.of_nat (TicketInit.slot_quantity finalslot)).
    { eapply TicketParsedInverse.parsed_success_extracts_identity_trace_zero_credit_and_accounting; eauto. }
    destruct EXTRACT as [HA [oldq [paidq [final [finalslot [finalops [total [HO [HP [TRACE [OUTPUT QUANTITY]]]]]]]]]]].
    split; [exact HA|].
    destruct (ticket_source_trace_live_note_accounting verify unpack handle operation issuer contents
      represents note_soundness txs state
      (TicketInit.held_value issuer contents (TicketInit.joined_slot oldq paidq))
      (TicketInit.incoming_credit paidq) [] final
      (TicketInit.held_value issuer contents finalslot) 0 finalops total TRACE oldnotes REPR)
      as [ns [HR LIABILITY]].
    rewrite HO,canonical_held_quantity in INITIAL.
    assert (STORED : liability ns <= Z.of_nat (TicketInit.slot_quantity finalslot)) by lia.
    exists oldq,paidq,final,finalslot,(rev finalops),ns.
    split; [exact HO|]. split; [exact HP|]. split; [exact OUTPUT|]. split; [exact HR|].
    split; [exact STORED|].
    intros inventory VALID OWNED.
    destruct finalslot as [q|].
    - destruct (OWNED q eq_refl) as [fragment [HI [HOWNER [HISSUER [HCONTENTS HQ]]]]].
      pose proof (certified_held_fragment_bounds_actual_reserve eq_value pool issuer contents
        inventory fragment HI HOWNER HISSUER HCONTENTS) as LOWER.
      rewrite HQ in LOWER. cbn [TicketInit.slot_quantity] in STORED. lia.
    - cbn [TicketInit.slot_quantity] in STORED.
      pose proof (owned_reserve_nonnegative eq_value pool issuer contents inventory). lia.
  Qed.
End ParsedCollateral.
Print Assumptions whole_parsed_ticket_success_produces_stored_and_owned_backing.
