(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith.
Require Import FullVM_WIP TicketPrimitives.
Import ListNotations.
Open Scope string_scope.

(* The checker binds this to parsed source. These are valid-identity initialization paths in
   the partial VM; the comparison and ticket-join callback meanings are explicit. *)
Definition identity_prefix (depth : nat) : list instruction :=
  [ReadTicket; Dup 1; Car; Dip 1 [Dup 1; Cdr; Car]; Pair;
   Dup depth; Prim "COMPARE_identity"; IsEq; If [] [Unit; Fail]].
Definition stored_guard : list instruction :=
  [IfNone [NoneValue] (identity_prefix 4 ++ [Drop; SomeValue])].
Definition paid_join : list instruction :=
  [Cdr; Cdr; Swap; Dig 4;
   IfNone [] [Pair; Prim "JOIN_ticket"; IfNone [Unit; Fail] []];
   SomeValue; Dug 3].
Definition join_code : list instruction := [Pair; Prim "JOIN_ticket"; IfNone [Unit; Fail] []].
Definition paid_body : list instruction := identity_prefix 7 ++ paid_join.
Definition init_after_amount : list instruction :=
  [Push (VMutez 0); CompareInt; IsEq; If [] [Unit; Fail]; UnpairN 4; Unpair;
   Dip 3 stored_guard; IfNone [Push (VNat 0)] paid_body; Dug 3].
Definition init_code : list instruction := [Nil; Swap; Prim "AMOUNT"] ++ init_after_amount.
Definition held_value (issuer contents : value) (slot : option nat) : value :=
  match slot with None => VNone | Some q => VSome (VTicket issuer contents q) end.
Definition joined_slot (old paid : option nat) : option nat :=
  match old, paid with
  | None, None => None | Some q, None | None, Some q => Some q
  | Some a, Some b => Some (a + b)%nat end.
Definition incoming_credit (paid : option nat) : nat :=
  match paid with None => 0%nat | Some q => q end.
Definition slot_quantity (slot : option nat) : nat :=
  match slot with None => 0%nat | Some q => q end.

Theorem joined_quantity_is_old_plus_received : forall old paid,
  slot_quantity (joined_slot old paid) = (slot_quantity old + incoming_credit paid)%nat.
Proof.
  intros [old|] [paid|]; cbn [slot_quantity joined_slot incoming_credit];
    try reflexivity. symmetry. apply Nat.add_0_r.
Qed.

Section Initialize.
  Variable primitive : string -> stack -> option stack.
  Hypothesis compare_same : forall asset rest,
    primitive "COMPARE_identity" (asset :: asset :: rest) = Some (VInt 0 :: rest).

  Lemma stored_identity_prefix : forall fuel issuer contents quantity ops frame,
    run primitive (8 + fuel)%nat (identity_prefix 4 ++ [Drop; SomeValue])
      (VTicket issuer contents quantity :: VPair issuer contents :: VList ops :: frame) =
    match primitive "COMPARE_identity"
      (VPair issuer contents :: VPair issuer contents ::
       VPair issuer (VPair contents (VNat quantity)) ::
       VTicket issuer contents quantity :: VPair issuer contents :: VList ops :: frame) with
    | Some s => run primitive (S fuel) [IsEq; If [] [Unit; Fail]; Drop; SomeValue] s
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma stored_guard_some_step : forall fuel issuer contents quantity ops frame,
    run primitive (2 + fuel)%nat stored_guard
      (VSome (VTicket issuer contents quantity) :: VPair issuer contents :: VList ops :: frame) =
    match run primitive (S fuel) (identity_prefix 4 ++ [Drop; SomeValue])
      (VTicket issuer contents quantity :: VPair issuer contents :: VList ops :: frame) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.

  Lemma stored_guard_none : forall asset ops frame,
    run primitive 140 stored_guard (VNone :: asset :: VList ops :: frame) =
    Some (VNone :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma stored_guard_valid_identity : forall issuer contents quantity ops frame,
    run primitive 140 stored_guard
      (VSome (VTicket issuer contents quantity) :: VPair issuer contents :: VList ops :: frame) =
    Some (VSome (VTicket issuer contents quantity) :: VPair issuer contents :: VList ops :: frame).
  Proof.
    intros. rewrite (stored_guard_some_step 138), (stored_identity_prefix 131), compare_same.
    reflexivity.
  Qed.

  Lemma paid_identity_prefix : forall fuel issuer contents quantity txs state held ops frame,
    run primitive (8 + fuel)%nat paid_body
      (VTicket issuer contents quantity :: VList txs :: state :: held ::
       VPair issuer contents :: VList ops :: frame) =
    match primitive "COMPARE_identity"
      (VPair issuer contents :: VPair issuer contents ::
       VPair issuer (VPair contents (VNat quantity)) ::
       VTicket issuer contents quantity :: VList txs :: state :: held ::
       VPair issuer contents :: VList ops :: frame) with
    | Some s => run primitive (S fuel) ([IsEq; If [] [Unit; Fail]] ++ paid_join) s
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma paid_identity_finish : forall fuel info ticket txs state held asset ops frame,
    run primitive (3 + fuel)%nat ([IsEq; If [] [Unit; Fail]] ++ paid_join)
      (VInt 0 :: info :: ticket :: VList txs :: state :: held :: asset :: VList ops :: frame) =
    run primitive (1 + fuel)%nat paid_join
      (info :: ticket :: VList txs :: state :: held :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma paid_join_empty : forall issuer contents amount txs state ops frame,
    run primitive 130 paid_join
      (VPair issuer (VPair contents (VNat amount)) :: VTicket issuer contents amount ::
       VList txs :: state :: VNone :: VPair issuer contents :: VList ops :: frame) =
    Some (VNat amount :: VList txs :: state :: VSome (VTicket issuer contents amount) ::
          VPair issuer contents :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma paid_empty_valid_identity : forall issuer contents amount txs state ops frame,
    run primitive 139 paid_body
      (VTicket issuer contents amount :: VList txs :: state :: VNone ::
       VPair issuer contents :: VList ops :: frame) =
    Some (VNat amount :: VList txs :: state :: VSome (VTicket issuer contents amount) ::
          VPair issuer contents :: VList ops :: frame).
  Proof.
    intros. rewrite (paid_identity_prefix 131), compare_same, (paid_identity_finish 129).
    apply paid_join_empty.
  Qed.

  Lemma paid_join_stored_step : forall fuel issuer contents left right txs state ops frame,
    run primitive (6 + fuel)%nat paid_join
      (VPair issuer (VPair contents (VNat right)) :: VTicket issuer contents right ::
       VList txs :: state :: VSome (VTicket issuer contents left) ::
       VPair issuer contents :: VList ops :: frame) =
    match run primitive (S fuel) join_code
      (VTicket issuer contents left :: VTicket issuer contents right :: VNat right ::
       VList txs :: state :: VPair issuer contents :: VList ops :: frame) with
    | Some s => run primitive (S fuel) [SomeValue; Dug 3] s | None => None end.
  Proof. reflexivity. Qed.

  Lemma join_prefix : forall fuel left right rest,
    run primitive (2 + fuel)%nat join_code (left :: right :: rest) =
    match primitive "JOIN_ticket" (VPair left right :: rest) with
    | Some s => run primitive fuel [IfNone [Unit; Fail] []] s | None => None end.
  Proof. reflexivity. Qed.

  Hypothesis join_same : forall issuer contents left right rest,
    primitive "JOIN_ticket"
      (VPair (VTicket issuer contents left) (VTicket issuer contents right) :: rest) =
    Some (VSome (VTicket issuer contents (left + right)) :: rest).

  Lemma paid_stored_valid_identity : forall issuer contents left right txs state ops frame,
    run primitive 139 paid_body
      (VTicket issuer contents right :: VList txs :: state ::
       VSome (VTicket issuer contents left) :: VPair issuer contents :: VList ops :: frame) =
    Some (VNat right :: VList txs :: state :: VSome (VTicket issuer contents (left + right)) ::
          VPair issuer contents :: VList ops :: frame).
  Proof.
    intros. rewrite (paid_identity_prefix 131), compare_same, (paid_identity_finish 129).
    rewrite (paid_join_stored_step 124), (join_prefix 123), join_same.
    reflexivity.
  Qed.

  Lemma init_amount_step : forall fuel tail input frame,
    run primitive (3 + fuel)%nat (init_code ++ tail) (input :: frame) =
    match primitive "AMOUNT" (input :: VList [] :: frame) with
    | Some s => run primitive fuel (init_after_amount ++ tail) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma init_guard_step : forall fuel tail paid txs state held asset frame,
    run primitive (7 + S fuel)%nat (init_after_amount ++ tail)
      (VMutez 0 :: VPair (VPair paid (VList txs)) (VPair state (VPair held asset)) :: VList [] :: frame) =
    match (match run primitive (S fuel) stored_guard (held :: asset :: VList [] :: frame) with
      | Some s => Some (paid :: VList txs :: state :: s) | None => None end) with
    | Some s => run primitive (S fuel)
        ([IfNone [Push (VNat 0)] paid_body; Dug 3] ++ tail)
        s
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma init_without_paid_step : forall fuel tail txs state held asset ops frame,
    run primitive (3 + fuel)%nat ([IfNone [Push (VNat 0)] paid_body; Dug 3] ++ tail)
      (VNone :: VList txs :: state :: held :: asset :: VList ops :: frame) =
    run primitive (1 + fuel)%nat tail
      (VList txs :: state :: held :: VNat 0 :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Lemma init_with_paid_step : forall fuel tail ticket txs state held asset ops frame,
    run primitive (S fuel) ([IfNone [Push (VNat 0)] paid_body; Dug 3] ++ tail)
      (VSome ticket :: VList txs :: state :: held :: asset :: VList ops :: frame) =
    match run primitive fuel paid_body
      (ticket :: VList txs :: state :: held :: asset :: VList ops :: frame) with
    | Some s => run primitive fuel (Dug 3 :: tail) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma init_credit_last_step : forall fuel tail credit txs state held asset ops frame,
    run primitive (S fuel) (Dug 3 :: tail)
      (VNat credit :: VList txs :: state :: held :: asset :: VList ops :: frame) =
    run primitive fuel tail
      (VList txs :: state :: held :: VNat credit :: asset :: VList ops :: frame).
  Proof. reflexivity. Qed.

  Hypothesis amount_zero : forall rest, primitive "AMOUNT" rest = Some (VMutez 0 :: rest).

  Local Opaque run.

  Theorem initializes_fixed_asset_and_received_credit :
    forall old paid issuer contents txs state tail frame,
    run primitive 150 (init_code ++ tail)
      (VPair (VPair (held_value issuer contents paid) (VList txs))
        (VPair state (VPair (held_value issuer contents old) (VPair issuer contents))) :: frame) =
    run primitive 138 tail
      (VList txs :: state :: held_value issuer contents (joined_slot old paid) ::
       VNat (incoming_credit paid) :: VPair issuer contents :: VList [] :: frame).
  Proof.
    intros old paid issuer contents txs state tail frame.
    rewrite (init_amount_step 147), amount_zero, (init_guard_step 139).
    destruct old as [left|]; cbn [held_value joined_slot].
    - rewrite stored_guard_valid_identity.
      destruct paid as [right|]; cbn [held_value incoming_credit].
      + rewrite (init_with_paid_step 139), paid_stored_valid_identity.
        apply (init_credit_last_step 138).
      + apply (init_without_paid_step 137).
    - rewrite stored_guard_none.
      destruct paid as [right|]; cbn [held_value incoming_credit].
      + rewrite (init_with_paid_step 139), paid_empty_valid_identity.
        apply (init_credit_last_step 138).
      + apply (init_without_paid_step 137).
  Qed.
End Initialize.

Print Assumptions stored_guard_valid_identity.
Print Assumptions paid_empty_valid_identity.
Print Assumptions paid_stored_valid_identity.
Print Assumptions initializes_fixed_asset_and_received_credit.
