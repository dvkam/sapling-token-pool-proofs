(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketPrimitives TicketWithdrawal TicketLoopBody LoopInduction.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Successful, guard-passing traces only. The ticket entering this loop has
   already been joined with any received ticket. Credit is the received amount
   not yet matched by shielding proofs. This does not prove initialization,
   identity guards, external operation execution or Michelson correspondence. *)
Inductive ticket_trace
  (verify : value -> value -> option (value * Z * value))
  (unpack handle : value -> option value) (operation : value -> value -> value)
  (issuer contents : value) :
  list value -> value -> value -> nat -> list value ->
  value -> value -> nat -> list value -> Z -> Prop :=
| ticket_nil : forall state held credit ops,
    ticket_trace verify unpack handle operation issuer contents
      [] state held credit ops state held credit ops 0
| ticket_partial : forall tx txs old quantity credit ops bytes balance next recipient receiver
                          final finalheld finalcredit finalops total,
    verify tx old = Some (bytes, balance, next) -> 0 < balance ->
    (Z.to_nat balance < quantity)%nat ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    ticket_trace verify unpack handle operation issuer contents txs next
      (VSome (VTicket issuer contents (quantity - Z.to_nat balance))) credit
      (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops)
      final finalheld finalcredit finalops total ->
    ticket_trace verify unpack handle operation issuer contents (tx :: txs) old
      (VSome (VTicket issuer contents quantity)) credit ops
      final finalheld finalcredit finalops (balance + total)
| ticket_full : forall tx txs old credit ops bytes balance next recipient receiver
                       final finalheld finalcredit finalops total,
    verify tx old = Some (bytes, balance, next) -> 0 < balance ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    ticket_trace verify unpack handle operation issuer contents txs next VNone credit
      (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops)
      final finalheld finalcredit finalops total ->
    ticket_trace verify unpack handle operation issuer contents (tx :: txs) old
      (VSome (VTicket issuer contents (Z.to_nat balance))) credit ops
      final finalheld finalcredit finalops (balance + total)
| ticket_nonpositive : forall tx txs old held credit ops balance next
                              final finalheld finalcredit finalops total,
    verify tx old = Some (VBytes [], balance, next) -> balance <= 0 ->
    (Z.to_nat (Z.abs balance) <= credit)%nat ->
    ticket_trace verify unpack handle operation issuer contents txs next held
      (credit - Z.to_nat (Z.abs balance)) ops
      final finalheld finalcredit finalops total ->
    ticket_trace verify unpack handle operation issuer contents (tx :: txs) old
      held credit ops final finalheld finalcredit finalops (balance + total).

Definition held_quantity (held : value) : nat :=
  match held with VSome (VTicket _ _ amount) => amount | _ => 0%nat end.

Theorem ticket_trace_credit_adjusted_conservation :
  forall verify unpack handle operation issuer contents txs old held credit ops
         next finalheld finalcredit finalops total,
  ticket_trace verify unpack handle operation issuer contents
    txs old held credit ops next finalheld finalcredit finalops total ->
  Z.of_nat (held_quantity held) - Z.of_nat credit - total =
  Z.of_nat (held_quantity finalheld) - Z.of_nat finalcredit.
Proof.
  intros verify unpack handle operation issuer contents txs old held credit ops
         next finalheld finalcredit finalops total H.
  induction H; cbn [held_quantity] in *.
  - lia.
  - rewrite Nat2Z.inj_sub in IHticket_trace by lia.
    rewrite Z2Nat.id in IHticket_trace by lia. lia.
  - rewrite Z2Nat.id by lia. lia.
  - rewrite Nat2Z.inj_sub in IHticket_trace by lia.
    rewrite Z2Nat.id in IHticket_trace by (apply Z.abs_nonneg).
    rewrite Z.abs_neq in IHticket_trace by lia. lia.
Qed.

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

  Lemma ticket_trace_iterates :
    forall txs old held credit ops next finalheld finalcredit finalops total,
    ticket_trace verify unpack handle operation issuer contents
      txs old held credit ops next finalheld finalcredit finalops total ->
    forall asset frame,
    iterate (fun tx s => run primitive 137 ticket_iteration (tx :: s)) txs
      (old :: held :: VNat credit :: asset :: VList ops :: frame) =
    Some (next :: finalheld :: VNat finalcredit :: asset :: VList finalops :: frame).
  Proof.
    intros txs old held credit ops next finalheld finalcredit finalops total H.
    induction H; intros asset frame; cbn [iterate].
    - reflexivity.
    - assert (STEP : run primitive 137 ticket_iteration
        (tx :: old :: VSome (VTicket issuer contents quantity) ::
         VNat credit :: asset :: VList ops :: frame) =
        Some (next :: VSome (VTicket issuer contents (quantity - Z.to_nat balance)) ::
          VNat credit :: asset ::
          VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame)).
      { eapply verified_ticket_partial_withdrawal_iteration; eauto. }
      rewrite STEP. apply IHticket_trace.
    - assert (STEP : run primitive 137 ticket_iteration
        (tx :: old :: VSome (VTicket issuer contents (Z.to_nat balance)) ::
         VNat credit :: asset :: VList ops :: frame) =
        Some (next :: VNone :: VNat credit :: asset ::
          VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame)).
      { eapply verified_ticket_full_withdrawal_iteration; eauto. }
      rewrite STEP. apply IHticket_trace.
    - assert (STEP : run primitive 137 ticket_iteration
        (tx :: old :: held :: VNat credit :: asset :: VList ops :: frame) =
        Some (next :: held :: VNat (credit - Z.to_nat (Z.abs balance)) :: asset :: VList ops :: frame)).
      { eapply verified_ticket_nonpositive_iteration; eauto. }
      rewrite STEP. apply IHticket_trace.
  Qed.

  Theorem unbounded_successful_ticket_batch :
    forall txs old held credit ops next finalheld finalcredit finalops total,
    ticket_trace verify unpack handle operation issuer contents
      txs old held credit ops next finalheld finalcredit finalops total ->
    forall asset frame,
    run primitive 138 [Iter ticket_iteration]
      (VList txs :: old :: held :: VNat credit :: asset :: VList ops :: frame) =
    Some (next :: finalheld :: VNat finalcredit :: asset :: VList finalops :: frame).
  Proof.
    intros txs old held credit ops next finalheld finalcredit finalops total H asset frame.
    rewrite (LoopInduction.source_loop_unbounded primitive ticket_iteration
      (fun tx s => run primitive 137 ticket_iteration (tx :: s)) 136) by reflexivity.
    eapply ticket_trace_iterates. exact H.
  Qed.
End Execution.

Print Assumptions ticket_trace_credit_adjusted_conservation.
Print Assumptions unbounded_successful_ticket_batch.
