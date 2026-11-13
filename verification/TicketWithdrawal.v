(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP TicketPrimitives.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* The positive ticket-withdrawal branch, pending parsed-source binding.
   This proves execution in the partial VM under explicit primitive equations.
   It does not prove the Octez interpreter, ticket linearity, rollback or gas. *)
Definition ticket_send_tail : list instruction :=
  [Push (VMutez 0); Swap; Prim "TRANSFER_ticket"; Dig 5; Swap; Cons; Dug 4].
Definition ticket_partial_tail : list instruction :=
  [Dig 2; Pair; Swap; Prim "SPLIT_ticket"; IfNone [Unit; Fail] [];
   Unpair; Swap; SomeValue; Dug 3].
Definition ticket_all_tail : list instruction :=
  [Drop; NoneValue; Dug 4; Swap; Drop].
Definition ticket_amount_tail : list instruction :=
  [ReadTicket; Cdr; Cdr; Dup 3; Swap; Sub; Dup 1; IsNat;
   IfNone [Unit; Fail] []; Swap; IsGt;
   If ticket_partial_tail ticket_all_tail] ++ ticket_send_tail.
Definition ticket_amount_dispatch : list instruction :=
  [IfNone [Unit; Fail] []; Swap; IsGt;
   If ticket_partial_tail ticket_all_tail] ++ ticket_send_tail.
Definition ticket_contract_tail : list instruction :=
  [IfNone [Unit; Fail] []; Swap; Dig 3; IfNone [Unit; Fail] []] ++ ticket_amount_tail.
Definition ticket_unpack_tail : list instruction :=
  [IfNone [Unit; Fail] []; Prim "CONTRACT_ticket"] ++ ticket_contract_tail.
Definition ticket_withdrawal : list instruction :=
  [Swap; Prim "UNPACK_address"; IfNone [Unit; Fail] [];
   Prim "CONTRACT_ticket"; IfNone [Unit; Fail] []; Swap;
   Dig 3; IfNone [Unit; Fail] []] ++ ticket_amount_tail.

Section TicketWithdrawal.
  Variable primitive : string -> stack -> option stack.
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

  Lemma ticket_unpack_step : forall fuel amount bytes state held credit asset ops frame,
    run primitive (2 + fuel)%nat ticket_withdrawal
      (VNat amount :: bytes :: state :: VSome held :: credit :: asset :: VList ops :: frame) =
    match primitive "UNPACK_address"
      (bytes :: VNat amount :: state :: VSome held :: credit :: asset :: VList ops :: frame) with
    | Some s => run primitive fuel ticket_unpack_tail s | None => None end.
  Proof. reflexivity. Qed.

  Lemma ticket_contract_step : forall fuel amount recipient state held credit asset ops frame,
    run primitive (2 + fuel)%nat ticket_unpack_tail
      (VSome recipient :: VNat amount :: state :: VSome held :: credit :: asset :: VList ops :: frame) =
    match primitive "CONTRACT_ticket"
      (recipient :: VNat amount :: state :: VSome held :: credit :: asset :: VList ops :: frame) with
    | Some s => run primitive fuel ticket_contract_tail s | None => None end.
  Proof. reflexivity. Qed.

  Lemma ticket_ready_step : forall fuel amount receiver state held credit asset ops frame,
    run primitive (5 + fuel)%nat ticket_contract_tail
      (VSome receiver :: VNat amount :: state :: VSome held :: credit :: asset :: VList ops :: frame) =
    run primitive (1 + fuel)%nat ticket_amount_tail
      (held :: VNat amount :: receiver :: state :: credit :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma ticket_send_exec : forall fuel ticket receiver state held credit identity ops frame,
    run primitive (8 + fuel)%nat ticket_send_tail
      (ticket :: receiver :: state :: held :: credit :: identity :: VList ops :: frame) =
    Some (state :: held :: credit :: identity ::
          VList (operation ticket receiver :: ops) :: frame).
  Proof.
    intros fuel ticket receiver state held credit asset ops frame.
    cbn [Nat.add ticket_send_tail run].
    rewrite transfer_frame. reflexivity.
  Qed.

  Lemma ticket_amount_step : forall fuel issuer contents quantity amount receiver state credit asset ops frame,
    run primitive (8 + fuel)%nat ticket_amount_tail
      (VTicket issuer contents quantity :: VNat amount :: receiver :: state :: credit :: asset :: VList ops :: frame) =
    let delta := Z.of_nat quantity - Z.of_nat amount in
    run primitive fuel ticket_amount_dispatch
      ((if Z.ltb delta 0 then VNone else VSome (VNat (Z.to_nat delta))) ::
       VInt delta :: VTicket issuer contents quantity :: VNat amount :: receiver ::
       state :: credit :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma ticket_dispatch_step : forall fuel remaining delta ticket amount receiver state credit asset ops frame,
    run primitive (5 + fuel)%nat ticket_amount_dispatch
      (VSome (VNat remaining) :: VInt delta :: ticket :: VNat amount :: receiver ::
       state :: credit :: asset :: VList ops :: frame) =
    match run primitive (1 + fuel)%nat
      (if Z.gtb delta 0 then ticket_partial_tail else ticket_all_tail)
      (VNat remaining :: ticket :: VNat amount :: receiver :: state :: credit :: asset :: VList ops :: frame) with
    | Some s => run primitive (1 + fuel)%nat ticket_send_tail s | None => None end.
  Proof. reflexivity. Qed.

  Lemma ticket_partial_exec : forall fuel issuer contents quantity amount remaining receiver state credit asset ops frame,
    (0 < amount)%nat -> (0 < remaining)%nat -> (amount + remaining = quantity)%nat ->
    run primitive (10 + fuel)%nat ticket_partial_tail
      (VNat remaining :: VTicket issuer contents quantity :: VNat amount :: receiver ::
       state :: credit :: asset :: VList ops :: frame) =
    Some (VTicket issuer contents amount :: receiver :: state ::
          VSome (VTicket issuer contents remaining) :: credit :: asset :: VList ops :: frame).
  Proof.
    intros fuel issuer contents quantity amount remaining receiver state credit asset ops frame A R S.
    cbn [Nat.add ticket_partial_tail run nth_error firstn skipn List.length app].
    rewrite split_frame.
    rewrite split_valid_amounts by assumption. reflexivity.
  Qed.

  Lemma ticket_all_exec : forall fuel issuer contents amount receiver state credit asset ops frame,
    run primitive (6 + fuel)%nat ticket_all_tail
      (VNat 0 :: VTicket issuer contents amount :: VNat amount :: receiver ::
       state :: credit :: asset :: VList ops :: frame) =
    Some (VTicket issuer contents amount :: receiver :: state :: VNone :: credit :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma ticket_negative_dispatch : forall fuel delta ticket amount receiver state credit asset ops frame,
    run primitive (4 + fuel)%nat ticket_amount_dispatch
      (VNone :: VInt delta :: ticket :: VNat amount :: receiver ::
       state :: credit :: asset :: VList ops :: frame) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.

  Lemma ticket_unpack_exec : forall amount bytes recipient receiver state held credit identity ops frame,
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    run primitive 128 ticket_withdrawal
      (VNat amount :: bytes :: state :: VSome held :: credit :: identity :: VList ops :: frame) =
    run primitive 120 ticket_amount_tail
      (held :: VNat amount :: receiver :: state :: credit :: identity :: VList ops :: frame).
  Proof.
    intros amount bytes recipient receiver state held credit identity ops frame U C.
    rewrite (ticket_unpack_step 126).
    rewrite (unpack_frame bytes recipient) by exact U.
    rewrite (ticket_contract_step 124).
    rewrite (contract_frame recipient receiver) by exact C.
    apply (ticket_ready_step 119).
  Qed.

  Theorem ticket_withdrawal_partial :
    forall amount quantity bytes recipient receiver issuer contents state credit identity ops frame,
    (0 < amount < quantity)%nat ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    run primitive 128 ticket_withdrawal
      (VNat amount :: bytes :: state :: VSome (VTicket issuer contents quantity) ::
       credit :: identity :: VList ops :: frame) =
    Some (state :: VSome (VTicket issuer contents (quantity - amount)) ::
          credit :: identity ::
          VList (operation (VTicket issuer contents amount) receiver :: ops) :: frame).
  Proof.
    intros amount quantity bytes recipient receiver issuer contents state credit identity ops frame A U C.
    rewrite (ticket_unpack_exec amount bytes recipient receiver) by assumption.
    assert (R : Z.of_nat quantity - Z.of_nat amount = Z.of_nat (quantity - amount))
      by (rewrite Nat2Z.inj_sub; lia).
    assert (N : Z.ltb (Z.of_nat (quantity - amount)) 0 = false)
      by (apply Z.ltb_ge; lia).
    assert (P : Z.gtb (Z.of_nat (quantity - amount)) 0 = true)
      by (apply Z.gtb_lt; lia).
    rewrite (ticket_amount_step 112). cbv zeta. rewrite R.
    rewrite N, Nat2Z.id.
    rewrite (ticket_dispatch_step 107), P.
    rewrite (ticket_partial_exec 98) by lia.
    apply (ticket_send_exec 100).
  Qed.

  Theorem ticket_withdrawal_all :
    forall amount bytes recipient receiver issuer contents state credit identity ops frame,
    (0 < amount)%nat ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    run primitive 128 ticket_withdrawal
      (VNat amount :: bytes :: state :: VSome (VTicket issuer contents amount) ::
       credit :: identity :: VList ops :: frame) =
    Some (state :: VNone :: credit :: identity ::
          VList (operation (VTicket issuer contents amount) receiver :: ops) :: frame).
  Proof.
    intros amount bytes recipient receiver issuer contents state credit identity ops frame A U C.
    rewrite (ticket_unpack_exec amount bytes recipient receiver) by assumption.
    rewrite (ticket_amount_step 112). cbv zeta. rewrite Z.sub_diag.
    rewrite Z.ltb_irrefl. cbn [Z.to_nat].
    rewrite (ticket_dispatch_step 107).
    replace (Z.gtb 0 0) with false by reflexivity.
    rewrite (ticket_all_exec 102).
    apply (ticket_send_exec 100).
  Qed.

  Theorem ticket_withdrawal_insufficient :
    forall amount quantity bytes recipient receiver issuer contents state credit identity ops frame,
    (quantity < amount)%nat ->
    unpack bytes = Some recipient -> handle recipient = Some receiver ->
    run primitive 128 ticket_withdrawal
      (VNat amount :: bytes :: state :: VSome (VTicket issuer contents quantity) ::
       credit :: identity :: VList ops :: frame) = None.
  Proof.
    intros amount quantity bytes recipient receiver issuer contents state credit identity ops frame A U C.
    rewrite (ticket_unpack_exec amount bytes recipient receiver) by assumption.
    assert (N : Z.ltb (Z.of_nat quantity - Z.of_nat amount) 0 = true)
      by (apply Z.ltb_lt; lia).
    rewrite (ticket_amount_step 112). cbv zeta. rewrite N.
    apply (ticket_negative_dispatch 108).
  Qed.
End TicketWithdrawal.

Print Assumptions ticket_withdrawal_partial.
Print Assumptions ticket_withdrawal_all.
Print Assumptions ticket_withdrawal_insufficient.
