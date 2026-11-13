From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketPrimitives TicketWithdrawal TicketLoopBody TicketMixedBatch TicketFinal.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Source-shaped ITER plus final credit guard and output. Initialization and
   identity, callback/Octez correspondence, and operation execution remain
   separate assumptions. *)
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


  Lemma loop_then_final_step : forall fuel txs old held credit asset ops frame,
    run primitive (S (S fuel)) (Iter ticket_iteration :: TicketFinal.final_code)
      (VList txs :: old :: held :: VNat credit :: asset :: VList ops :: frame) =
    match iterate (fun tx s => run primitive (S fuel) ticket_iteration (tx :: s))
      txs (old :: held :: VNat credit :: asset :: VList ops :: frame) with
    | Some out => run primitive (S fuel) TicketFinal.final_code out | None => None end.
  Proof. reflexivity. Qed.

  Theorem successful_batch_then_final :
    forall txs old held credit ops next finalheld finalops total asset frame,
    ticket_trace verify unpack handle operation issuer contents
      txs old held credit ops next finalheld 0 finalops total ->
    run primitive 138 (Iter ticket_iteration :: TicketFinal.final_code)
      (VList txs :: old :: held :: VNat credit :: asset :: VList ops :: frame) =
    Some (VPair (VList (rev finalops)) (VPair next (VPair finalheld asset)) :: frame) /\
    (Z.of_nat (held_quantity held) - Z.of_nat credit - total =
     Z.of_nat (held_quantity finalheld))%Z.
  Proof.
    intros txs old held credit ops next finalheld finalops total asset frame H.
    split.
    - assert (ITER : iterate (fun tx s => run primitive 137 ticket_iteration (tx :: s)) txs
          (old :: held :: VNat credit :: asset :: VList ops :: frame) =
        Some (next :: finalheld :: VNat 0 :: asset :: VList finalops :: frame)).
      { eapply TicketMixedBatch.ticket_trace_iterates; eauto. }
      rewrite (loop_then_final_step 136), ITER.
      apply (TicketFinal.zero_credit_returns_at_fuel primitive 97).
    - pose proof (TicketMixedBatch.ticket_trace_credit_adjusted_conservation
        verify unpack handle operation issuer contents txs old held credit ops
        next finalheld 0 finalops total H) as HC.
      simpl in HC. lia.
  Qed.
End Execution.
Print Assumptions successful_batch_then_final.
