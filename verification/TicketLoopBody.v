(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP TicketPrimitives TicketWithdrawal.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* Source-shaped ticket transaction body. Primitive frame equations and the
   translation to Michelson remain explicit external obligations. Successful
   steps preserve the supplied identity value but do not establish that the
   initial held ticket or the Sapling state has that identity or backing. *)
Definition ticket_empty_bound_guard : list instruction :=
  [Size; Push (VNat 0); CompareInt; IsEq; If [] [Unit; Fail]].
Definition ticket_credit_ready : list instruction :=
  [IfNone [Unit; Fail] []; Dug 3] ++ ticket_empty_bound_guard.
Definition ticket_nonpositive : list instruction :=
  [Dig 4; Sub; IsNat] ++ ticket_credit_ready.
Definition ticket_iteration : list instruction :=
  [Prim "SAPLING_VERIFY_UPDATE"; IfNone [Unit; Fail] []; UnpairN 3;
   Swap; Dup 1; Abs; Swap; IsGt;
   If ticket_withdrawal ticket_nonpositive].

Section TicketLoopBody.
  Variable primitive : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Hypothesis verify_frame : forall tx old bound balance next rest,
    verify tx old = Some (bound, balance, next) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).

  Lemma ticket_verify_step : forall fuel tx old held credit asset ops frame,
    run primitive (S fuel) ticket_iteration
      (tx :: old :: held :: VNat credit :: asset :: VList ops :: frame) =
    match primitive "SAPLING_VERIFY_UPDATE"
      (tx :: old :: held :: VNat credit :: asset :: VList ops :: frame) with
    | Some s => run primitive fuel (tl ticket_iteration) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma ticket_numeric_step : forall fuel bound balance next held credit asset ops frame,
    run primitive (8 + S fuel)%nat (tl ticket_iteration)
      (VSome (VPair bound (VPair (VInt balance) next)) ::
       held :: VNat credit :: asset :: VList ops :: frame) =
    match run primitive (S fuel)
      (if Z.gtb balance 0 then ticket_withdrawal else ticket_nonpositive)
      (VNat (Z.to_nat (Z.abs balance)) :: bound :: next :: held ::
       VNat credit :: asset :: VList ops :: frame) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.

  Lemma ticket_credit_step : forall fuel amount credit bound state held asset ops frame,
    run primitive (3 + fuel)%nat ticket_nonpositive
      (VNat amount :: bound :: state :: held :: VNat credit :: asset :: VList ops :: frame) =
    let delta := Z.of_nat credit - Z.of_nat amount in
    run primitive fuel ticket_credit_ready
      ((if Z.ltb delta 0 then VNone else VSome (VNat (Z.to_nat delta))) ::
       bound :: state :: held :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma ticket_credit_ready_step : forall fuel remaining bound state held asset ops frame,
    run primitive (3 + fuel)%nat ticket_credit_ready
      (VSome (VNat remaining) :: bound :: state :: held :: asset :: VList ops :: frame) =
    run primitive (1 + fuel)%nat ticket_empty_bound_guard
      (bound :: state :: held :: VNat remaining :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma ticket_empty_bound_step : forall fuel state held remaining asset ops frame,
    run primitive (6 + fuel)%nat ticket_empty_bound_guard
      (VBytes [] :: state :: held :: VNat remaining :: asset :: VList ops :: frame) =
    Some (state :: held :: VNat remaining :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma ticket_credit_failure_step : forall fuel bound state held asset ops frame,
    run primitive (4 + fuel)%nat ticket_credit_ready
      (VNone :: bound :: state :: held :: asset :: VList ops :: frame) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.

  Theorem ticket_nonpositive_consumes_only_received_credit :
    forall amount credit state held asset ops frame,
    (amount <= credit)%nat ->
    run primitive 128 ticket_nonpositive
      (VNat amount :: VBytes [] :: state :: held :: VNat credit :: asset :: VList ops :: frame) =
    Some (state :: held :: VNat (credit - amount) :: asset :: VList ops :: frame).
  Proof.
    intros amount credit state held asset ops frame A.
    assert (R : Z.of_nat credit - Z.of_nat amount = Z.of_nat (credit - amount))
      by (rewrite Nat2Z.inj_sub; lia).
    assert (N : Z.ltb (Z.of_nat (credit - amount)) 0 = false)
      by (apply Z.ltb_ge; lia).
    rewrite (ticket_credit_step 125). cbv zeta. rewrite R, N, Nat2Z.id.
    rewrite (ticket_credit_ready_step 122).
    apply (ticket_empty_bound_step 117).
  Qed.

  Theorem ticket_nonpositive_rejects_excess_credit_consumption :
    forall amount credit state held asset ops frame,
    (credit < amount)%nat ->
    run primitive 128 ticket_nonpositive
      (VNat amount :: VBytes [] :: state :: held :: VNat credit :: asset :: VList ops :: frame) = None.
  Proof.
    intros amount credit state held asset ops frame A.
    assert (N : Z.ltb (Z.of_nat credit - Z.of_nat amount) 0 = true)
      by (apply Z.ltb_lt; lia).
    rewrite (ticket_credit_step 125). cbv zeta. rewrite N.
    apply (ticket_credit_failure_step 121).
  Qed.

  Theorem verified_ticket_nonpositive_iteration :
    forall tx old balance next held credit asset ops frame,
    verify tx old = Some (VBytes [], balance, next) -> balance <= 0 ->
    (Z.to_nat (Z.abs balance) <= credit)%nat ->
    run primitive 137 ticket_iteration
      (tx :: old :: held :: VNat credit :: asset :: VList ops :: frame) =
    Some (next :: held :: VNat (credit - Z.to_nat (Z.abs balance)) :: asset :: VList ops :: frame).
  Proof.
    intros tx old balance next held credit asset ops frame V B A.
    assert (G : Z.gtb balance 0 = false).
    { apply Bool.not_true_is_false. intro H. apply Z.gtb_lt in H. lia. }
    rewrite (ticket_verify_step 136), (verify_frame tx old (VBytes []) balance next) by exact V.
    rewrite (ticket_numeric_step 127), G.
    rewrite ticket_nonpositive_consumes_only_received_credit by exact A.
    reflexivity.
  Qed.

  Variable unpack : value -> option value.
  Variable handle : value -> option value.
  Variable operation : value -> value -> value.
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

  Theorem verified_ticket_partial_withdrawal_iteration :
    forall tx old balance next quantity bytes recipient receiver issuer contents credit asset ops frame,
    verify tx old = Some (bytes, balance, next) -> 0 < balance ->
    (Z.to_nat balance < quantity)%nat ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    run primitive 137 ticket_iteration
      (tx :: old :: VSome (VTicket issuer contents quantity) ::
       VNat credit :: asset :: VList ops :: frame) =
    Some (next :: VSome (VTicket issuer contents (quantity - Z.to_nat balance)) ::
          VNat credit :: asset ::
          VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame).
  Proof.
    intros tx old balance next quantity bytes recipient receiver issuer contents credit asset ops frame V B Q U C.
    assert (G : Z.gtb balance 0 = true) by (apply Z.gtb_lt; exact B).
    assert (A : Z.to_nat (Z.abs balance) = Z.to_nat balance) by (rewrite Z.abs_eq; lia).
    rewrite (ticket_verify_step 136), (verify_frame tx old bytes balance next) by exact V.
    rewrite (ticket_numeric_step 127), G, A.
    rewrite (ticket_withdrawal_partial primitive unpack handle operation
      unpack_frame contract_frame split_frame transfer_frame
      (Z.to_nat balance) quantity bytes recipient receiver) by (try assumption; lia).
    reflexivity.
  Qed.

  Theorem verified_ticket_full_withdrawal_iteration :
    forall tx old balance next bytes recipient receiver issuer contents credit asset ops frame,
    verify tx old = Some (bytes, balance, next) -> 0 < balance ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    run primitive 137 ticket_iteration
      (tx :: old :: VSome (VTicket issuer contents (Z.to_nat balance)) ::
       VNat credit :: asset :: VList ops :: frame) =
    Some (next :: VNone :: VNat credit :: asset ::
          VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame).
  Proof.
    intros tx old balance next bytes recipient receiver issuer contents credit asset ops frame V B U C.
    assert (G : Z.gtb balance 0 = true) by (apply Z.gtb_lt; exact B).
    assert (A : Z.to_nat (Z.abs balance) = Z.to_nat balance) by (rewrite Z.abs_eq; lia).
    rewrite (ticket_verify_step 136), (verify_frame tx old bytes balance next) by exact V.
    rewrite (ticket_numeric_step 127), G, A.
    assert (W : run primitive 128 ticket_withdrawal
      (VNat (Z.to_nat balance) :: bytes :: next ::
       VSome (VTicket issuer contents (Z.to_nat balance)) ::
       VNat credit :: asset :: VList ops :: frame) =
      Some (next :: VNone :: VNat credit :: asset ::
        VList (operation (VTicket issuer contents (Z.to_nat balance)) receiver :: ops) :: frame)).
    { eapply ticket_withdrawal_all; eauto; lia. }
    rewrite W. reflexivity.
  Qed.
End TicketLoopBody.

Print Assumptions ticket_nonpositive_consumes_only_received_credit.
Print Assumptions ticket_nonpositive_rejects_excess_credit_consumption.
Print Assumptions verified_ticket_nonpositive_iteration.
Print Assumptions verified_ticket_partial_withdrawal_iteration.
Print Assumptions verified_ticket_full_withdrawal_iteration.
