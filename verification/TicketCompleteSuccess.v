From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketPrimitives TicketWithdrawal TicketLoopBody TicketMixedBatch TicketFinal TicketPostBatch TicketInit.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Whole modeled ticket program for valid fixed-identity initialization and
   successful traces ending with zero received credit. Primitive semantics,
   typed ticket validity, source translation, Sapling validity and execution
   of operations remain explicit external obligations. *)
Definition full_code : list instruction :=
  TicketInit.init_code ++ Iter TicketLoopBody.ticket_iteration :: TicketFinal.final_code.

Lemma held_quantity_of_slot : forall issuer contents slot,
  held_quantity (TicketInit.held_value issuer contents slot) = TicketInit.slot_quantity slot.
Proof. intros; destruct slot; reflexivity. Qed.

Section Execution.
  Variable primitive : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack handle : value -> option value.
  Variable operation : value -> value -> value.
  Variable issuer contents : value.
  Hypothesis verify_frame : forall tx old bound balance next rest,
    verify tx old = Some (bound, balance, next) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis unpack_frame : forall bytes recipient rest,
    unpack bytes = Some recipient ->
    primitive "UNPACK_address" (bytes :: rest) = Some (VSome recipient :: rest).
  Hypothesis contract_frame : forall recipient receiver rest,
    handle recipient = Some receiver ->
    primitive "CONTRACT_ticket" (recipient :: rest) = Some (VSome receiver :: rest).
  Hypothesis split_frame : forall issuer contents quantity left right rest,
    primitive "SPLIT_ticket"
      (VTicket issuer contents quantity :: VPair (VNat left) (VNat right) :: rest) =
    Some (split_ticket (VTicket issuer contents quantity) left right :: rest).
  Hypothesis transfer_frame : forall ticket receiver rest,
    primitive "TRANSFER_ticket" (ticket :: VMutez 0 :: receiver :: rest) =
    Some (operation ticket receiver :: rest).



  Hypothesis compare_same : forall asset rest,
    primitive "COMPARE_identity" (asset :: asset :: rest) = Some (VInt 0 :: rest).
  Hypothesis join_same : forall issuer0 contents0 left right rest,
    primitive "JOIN_ticket"
      (VPair (VTicket issuer0 contents0 left) (VTicket issuer0 contents0 right) :: rest) =
    Some (VSome (VTicket issuer0 contents0 (left + right)) :: rest).
  Hypothesis amount_zero : forall rest, primitive "AMOUNT" rest = Some (VMutez 0 :: rest).

  Theorem whole_successful_ticket_batch :
    forall old paid txs state final finalheld finalops total frame,
    ticket_trace verify unpack handle operation issuer contents txs state
      (TicketInit.held_value issuer contents (TicketInit.joined_slot old paid))
      (TicketInit.incoming_credit paid) [] final finalheld 0 finalops total ->
    run primitive 150 full_code
      (VPair (VPair (TicketInit.held_value issuer contents paid) (VList txs))
        (VPair state (VPair (TicketInit.held_value issuer contents old) (VPair issuer contents))) :: frame) =
    Some (VPair (VList (rev finalops)) (VPair final (VPair finalheld (VPair issuer contents))) :: frame) /\
    (Z.of_nat (TicketInit.slot_quantity old) - total = Z.of_nat (held_quantity finalheld))%Z.
  Proof.
    intros old paid txs state final finalheld finalops total frame H.
    assert (POST :
      run primitive 138 (Iter ticket_iteration :: TicketFinal.final_code)
        (VList txs :: state ::
         TicketInit.held_value issuer contents (TicketInit.joined_slot old paid) ::
         VNat (TicketInit.incoming_credit paid) :: VPair issuer contents :: VList [] :: frame) =
      Some (VPair (VList (rev finalops)) (VPair final (VPair finalheld (VPair issuer contents))) :: frame) /\
      (Z.of_nat (held_quantity (TicketInit.held_value issuer contents (TicketInit.joined_slot old paid))) -
       Z.of_nat (TicketInit.incoming_credit paid) - total = Z.of_nat (held_quantity finalheld))%Z).
    { eapply TicketPostBatch.successful_batch_then_final; eauto. }
    destruct POST as [Hrun Haccount]. split.
    - unfold full_code.
      rewrite (TicketInit.initializes_fixed_asset_and_received_credit primitive compare_same join_same amount_zero).
      exact Hrun.
    - rewrite held_quantity_of_slot, TicketInit.joined_quantity_is_old_plus_received, Nat2Z.inj_add in Haccount.
      lia.
  Qed.
End Execution.
Print Assumptions whole_successful_ticket_batch.
