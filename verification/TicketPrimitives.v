(* SPDX-License-Identifier: MIT *)
From Coq Require Import List Arith Bool Lia.
Require Import FullVM_WIP.
Import ListNotations.
Local Open Scope nat_scope.

(* Models the positive ticket amounts and split/join field updates in pinned
   script_interpreter.ml:1647-1685 and ticket_amount.ml. This is not a proved
   refinement of those OCaml functions or a whole ticket-pool proof. The
   equality decider represents correct equality of ticketer and comparable
   contents. Linear ownership, gas and protocol rollback are outside this VM. *)
Section TicketPrimitives.
  Variable equal_value : forall x y : value, {x = y} + {x <> y}.

  Definition join_ticket (left right : value) : value :=
    match left, right with
    | VTicket issuer contents quantity, VTicket issuer' contents' quantity' =>
        if equal_value issuer issuer' then
          if equal_value contents contents' then
            VSome (VTicket issuer contents (quantity + quantity'))
          else VNone
        else VNone
    | _, _ => VNone
    end.

  Definition split_ticket (ticket : value) (left right : nat) : value :=
    match ticket with
    | VTicket issuer contents quantity =>
        if ((0 <? left) && (0 <? right)) && ((left + right) =? quantity) then
          VSome (VPair (VTicket issuer contents left)
                       (VTicket issuer contents right))
        else VNone
    | _ => VNone
    end.

  Definition well_formed_ticket (ticket : value) : Prop :=
    match ticket with VTicket _ _ quantity => 0 < quantity | _ => False end.

  Theorem join_preserves_identity_and_quantity :
    forall issuer contents quantity issuer' contents' quantity'
           result_issuer result_contents total,
    join_ticket (VTicket issuer contents quantity)
                (VTicket issuer' contents' quantity') =
      VSome (VTicket result_issuer result_contents total) ->
    issuer = issuer' /\ contents = contents' /\
    result_issuer = issuer /\ result_contents = contents /\
    total = quantity + quantity'.
  Proof.
    intros issuer contents quantity issuer' contents' quantity'
           result_issuer result_contents total H.
    unfold join_ticket in H.
    destruct (equal_value issuer issuer'); try discriminate.
    destruct (equal_value contents contents'); try discriminate.
    inversion H; subst; repeat split; reflexivity.
  Qed.

  Theorem join_same_identity : forall issuer contents left right,
    join_ticket (VTicket issuer contents left) (VTicket issuer contents right) =
    VSome (VTicket issuer contents (left + right)).
  Proof.
    intros; unfold join_ticket.
    destruct (equal_value issuer issuer); try contradiction.
    destruct (equal_value contents contents); try contradiction.
    reflexivity.
  Qed.

  Theorem join_rejects_foreign_identity :
    forall issuer contents quantity issuer' contents' quantity',
    (issuer <> issuer' \/ contents <> contents') ->
    join_ticket (VTicket issuer contents quantity)
                (VTicket issuer' contents' quantity') = VNone.
  Proof.
    intros; unfold join_ticket.
    destruct (equal_value issuer issuer');
      try (destruct (equal_value contents contents')); intuition.
  Qed.

  Theorem split_preserves_identity_and_quantity :
    forall issuer contents quantity left right a b,
    split_ticket (VTicket issuer contents quantity) left right =
      VSome (VPair a b) ->
    a = VTicket issuer contents left /\
    b = VTicket issuer contents right /\
    left + right = quantity /\ 0 < left /\ 0 < right.
  Proof.
    intros issuer contents quantity left right a b H.
    unfold split_ticket in H.
    destruct (((0 <? left) && (0 <? right)) && ((left + right) =? quantity))
      eqn:E; try discriminate.
    apply andb_true_iff in E as [P Sum].
    apply andb_true_iff in P as [L R].
    apply Nat.ltb_lt in L; apply Nat.ltb_lt in R.
    apply Nat.eqb_eq in Sum.
    inversion H; subst; repeat split; auto.
  Qed.

  Theorem split_valid_amounts : forall issuer contents quantity left right,
    0 < left -> 0 < right -> left + right = quantity ->
    split_ticket (VTicket issuer contents quantity) left right =
      VSome (VPair (VTicket issuer contents left)
                   (VTicket issuer contents right)).
  Proof.
    intros issuer contents quantity left right L R Sum.
    unfold split_ticket.
    assert ((0 <? left) = true) by (apply Nat.ltb_lt; exact L).
    assert ((0 <? right) = true) by (apply Nat.ltb_lt; exact R).
    assert (((left + right) =? quantity) = true) by (apply Nat.eqb_eq; exact Sum).
    now rewrite H, H0, H1.
  Qed.

  Theorem split_zero_left_rejected : forall issuer contents quantity right,
    split_ticket (VTicket issuer contents quantity) 0 right = VNone.
  Proof. reflexivity. Qed.

  Theorem split_zero_right_rejected : forall issuer contents quantity left,
    split_ticket (VTicket issuer contents quantity) left 0 = VNone.
  Proof.
    intros; unfold split_ticket; rewrite Nat.ltb_irrefl, andb_false_r;
      reflexivity.
  Qed.

  Theorem split_then_join : forall issuer contents quantity left right,
    0 < left -> 0 < right -> left + right = quantity ->
    split_ticket (VTicket issuer contents quantity) left right =
      VSome (VPair (VTicket issuer contents left) (VTicket issuer contents right)) /\
    join_ticket (VTicket issuer contents left) (VTicket issuer contents right) =
      VSome (VTicket issuer contents quantity).
  Proof.
    intros; split.
    - now apply split_valid_amounts.
    - rewrite join_same_identity. now rewrite H1.
  Qed.

  Theorem joined_amount_is_positive : forall issuer contents left right,
    0 < left -> 0 < right ->
    well_formed_ticket (VTicket issuer contents (left + right)).
  Proof. intros; cbn [well_formed_ticket]; lia. Qed.

  Theorem read_ticket_keeps_original : forall primitive issuer contents quantity frame,
    run primitive 4 [ReadTicket] (VTicket issuer contents quantity :: frame) =
      Some (VPair issuer (VPair contents (VNat quantity)) ::
            VTicket issuer contents quantity :: frame).
  Proof. reflexivity. Qed.
End TicketPrimitives.

Print Assumptions join_preserves_identity_and_quantity.
Print Assumptions join_rejects_foreign_identity.
Print Assumptions split_preserves_identity_and_quantity.
Print Assumptions split_then_join.
Print Assumptions read_ticket_keeps_original.
