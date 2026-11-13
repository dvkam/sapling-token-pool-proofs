From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP TicketInit.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Arbitrary optional typed-shaped tickets, with identity and quantity not
   assumed to match the configured asset. Positivity/linearity and protocol
   correspondence remain external obligations. *)
Definition ticket_slot := option (value * value * nat).
Definition slot_value (slot : ticket_slot) : value :=
  match slot with
  | None => VNone
  | Some (issuer,contents,quantity) => VSome (VTicket issuer contents quantity)
  end.

Section InitInverse.
  Variable prim : string -> stack -> option stack.
  Variable compare_value : value -> value -> Z.
  Variable amount : nat.
  Hypothesis compare_frame : forall left right rest,
    prim "COMPARE_identity" (left :: right :: rest) =
      Some (VInt (compare_value left right) :: rest).
  Hypothesis compare_zero : forall left right,
    compare_value left right = 0 <-> left = right.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez amount :: rest).
  Hypothesis join_same : forall issuer contents left right rest,
    prim "JOIN_ticket" (VPair (VTicket issuer contents left) (VTicket issuer contents right) :: rest) =
      Some (VSome (VTicket issuer contents (left + right)) :: rest).

  Lemma compare_same : forall asset rest,
    prim "COMPARE_identity" (asset :: asset :: rest) = Some (VInt 0 :: rest).
  Proof. intros; rewrite compare_frame. rewrite (proj2 (compare_zero asset asset) eq_refl). reflexivity. Qed.

  Lemma stored_guard_any : forall fuel ti tc qty issuer contents ops frame,
    run prim (2 + fuel)%nat stored_guard
      (VSome (VTicket ti tc qty) :: VPair issuer contents :: VList ops :: frame) =
    match run prim (S fuel) (identity_prefix 4 ++ [Drop;SomeValue])
      (VTicket ti tc qty :: VPair issuer contents :: VList ops :: frame) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.

  Lemma stored_identity_any : forall fuel ti tc qty issuer contents ops frame,
    run prim (8 + fuel)%nat (identity_prefix 4 ++ [Drop;SomeValue])
      (VTicket ti tc qty :: VPair issuer contents :: VList ops :: frame) =
    match prim "COMPARE_identity"
      (VPair issuer contents :: VPair ti tc :: VPair ti (VPair tc (VNat qty)) ::
       VTicket ti tc qty :: VPair issuer contents :: VList ops :: frame) with
    | Some s => run prim (S fuel) [IsEq;If [] [Unit;Fail];Drop;SomeValue] s | None => None end.
  Proof. reflexivity. Qed.

  Lemma iseq_step : forall fuel tail z rest,
    run prim (S fuel) (IsEq :: tail) (VInt z :: rest) =
    run prim fuel tail (VBool (Z.eqb z 0) :: rest).
  Proof. reflexivity. Qed.

  Lemma stored_check_false : forall fuel z rest,
    Z.eqb z 0 = false ->
    run prim (4 + fuel)%nat [IsEq; If [] [Unit;Fail]; Drop; SomeValue] (VInt z :: rest) = None.
  Proof. intros fuel z rest H; rewrite (iseq_step (3 + fuel)%nat), H; reflexivity. Qed.

  Local Opaque run.

  Lemma stored_success_identity : forall ti tc qty issuer contents ops frame result,
    run prim 140 stored_guard
      (VSome (VTicket ti tc qty) :: VPair issuer contents :: VList ops :: frame) = Some result ->
    ti = issuer /\ tc = contents /\
    result = VSome (VTicket issuer contents qty) :: VPair issuer contents :: VList ops :: frame.
  Proof.
    intros ti tc qty issuer contents ops frame result H.
    pose proof H as Hguard.
    rewrite (stored_guard_any 138), (stored_identity_any 131), compare_frame in H.
    destruct (Z.eqb (compare_value (VPair issuer contents) (VPair ti tc)) 0) eqn:E.
    - apply Z.eqb_eq in E. apply compare_zero in E. injection E as EI EC. subst.
      rewrite (TicketInit.stored_guard_valid_identity prim compare_same) in Hguard.
      inversion Hguard; subst; auto.
    - rewrite (stored_check_false 128) in H by exact E. discriminate.
  Qed.

  Lemma paid_prefix_any : forall fuel ti tc qty issuer contents txs state held ops frame,
    run prim (8 + fuel)%nat paid_body
      (VTicket ti tc qty :: VList txs :: state :: held :: VPair issuer contents :: VList ops :: frame) =
    match prim "COMPARE_identity"
      (VPair issuer contents :: VPair ti tc :: VPair ti (VPair tc (VNat qty)) ::
       VTicket ti tc qty :: VList txs :: state :: held :: VPair issuer contents :: VList ops :: frame) with
    | Some s => run prim (S fuel) ([IsEq; If [] [Unit;Fail]] ++ paid_join) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma paid_check_false : forall fuel z rest,
    Z.eqb z 0 = false ->
    run prim (4 + fuel)%nat ([IsEq; If [] [Unit;Fail]] ++ paid_join) (VInt z :: rest) = None.
  Proof.
    intros fuel z rest H.
    change (run prim (4 + fuel)%nat (IsEq :: If [] [Unit;Fail] :: paid_join) (VInt z :: rest) = None).
    rewrite (iseq_step (3 + fuel)%nat), H; reflexivity.
  Qed.

  Lemma paid_success_identity : forall ti tc qty issuer contents txs state held ops frame result,
    run prim 139 paid_body
      (VTicket ti tc qty :: VList txs :: state :: held :: VPair issuer contents :: VList ops :: frame) = Some result ->
    ti = issuer /\ tc = contents.
  Proof.
    intros ti tc qty issuer contents txs state held ops frame result H.
    rewrite (paid_prefix_any 131), compare_frame in H.
    destruct (Z.eqb (compare_value (VPair issuer contents) (VPair ti tc)) 0) eqn:E.
    - apply Z.eqb_eq in E. apply compare_zero in E. injection E as EI EC. split; symmetry; assumption.
    - rewrite (paid_check_false 128) in H by exact E. discriminate.
  Qed.

  Lemma stored_slot_inverse : forall old issuer contents ops frame result,
    run prim 140 stored_guard
      (slot_value old :: VPair issuer contents :: VList ops :: frame) = Some result ->
    exists oldq, slot_value old = held_value issuer contents oldq /\
      result = held_value issuer contents oldq :: VPair issuer contents :: VList ops :: frame.
  Proof.
    intros old issuer contents ops frame result H.
    destruct old as [[[ti tc] qty]|]; cbn [slot_value] in *.
    - destruct (stored_success_identity ti tc qty issuer contents ops frame result H)
        as [EI [EC ER]]. subst ti tc.
      exists (Some qty). cbn [held_value]. split; [reflexivity|exact ER].
    - rewrite (TicketInit.stored_guard_none prim) in H.
      inversion H; subst. exists None. split; reflexivity.
  Qed.

  Lemma paid_branch_identity : forall paid txs state held issuer contents tail frame output,
    run prim 140 ([IfNone [Push (VNat 0)] paid_body; Dug 3] ++ tail)
      (slot_value paid :: VList txs :: state :: held :: VPair issuer contents :: VList [] :: frame) = Some output ->
    exists paidq, slot_value paid = held_value issuer contents paidq.
  Proof.
    intros paid txs state held issuer contents tail frame output H.
    destruct paid as [[[ti tc] qty]|]; cbn [slot_value] in *.
    - rewrite (TicketInit.init_with_paid_step prim 139) in H.
      destruct (run prim 139 paid_body
        (VTicket ti tc qty :: VList txs :: state :: held :: VPair issuer contents :: VList [] :: frame))
        as [result|] eqn:HP; [|discriminate].
      destruct (paid_success_identity ti tc qty issuer contents txs state held [] frame result HP) as [EI EC].
      subst ti tc. exists (Some qty). reflexivity.
    - exists None. reflexivity.
  Qed.

  Lemma init_nonzero_rejects : forall fuel n input tail frame,
    run prim (8 + fuel)%nat (init_after_amount ++ tail)
      (VMutez (S n) :: input :: VList [] :: frame) = None.
  Proof. reflexivity. Qed.

  Theorem successful_initialization_extracts_identity_and_tail :
    forall old paid issuer contents txs state tail frame output,
    run prim 150 (init_code ++ tail)
      (VPair (VPair (slot_value paid) (VList txs))
        (VPair state (VPair (slot_value old) (VPair issuer contents))) :: frame) = Some output ->
    amount = 0%nat /\
    exists oldq paidq,
      slot_value old = held_value issuer contents oldq /\
      slot_value paid = held_value issuer contents paidq /\
      run prim 138 tail
        (VList txs :: state :: held_value issuer contents (joined_slot oldq paidq) ::
         VNat (incoming_credit paidq) :: VPair issuer contents :: VList [] :: frame) = Some output.
  Proof.
    intros old paid issuer contents txs state tail frame output HR.
    pose proof HR as H.
    rewrite (TicketInit.init_amount_step prim 147), amount_frame in H.
    destruct amount as [|n].
    2: { rewrite (init_nonzero_rejects 139 n) in H. discriminate. }
    split; [reflexivity|].
    rewrite (TicketInit.init_guard_step prim 139) in H.
    destruct (run prim 140 stored_guard
      (slot_value old :: VPair issuer contents :: VList [] :: frame)) as [stored|] eqn:HS; [|discriminate].
    destruct (stored_slot_inverse old issuer contents [] frame stored HS) as [oldq [HOLD ESTORED]].
    subst stored.
    destruct (paid_branch_identity paid txs state (held_value issuer contents oldq) issuer contents tail frame output H)
      as [paidq HPAID].
    exists oldq, paidq. split; [exact HOLD|]. split; [exact HPAID|].
    rewrite HOLD, HPAID in HR.
    assert (Hamount : forall rest, prim "AMOUNT" rest = Some (VMutez 0 :: rest)).
    { exact amount_frame. }
    rewrite (TicketInit.initializes_fixed_asset_and_received_credit prim compare_same join_same Hamount) in HR.
    exact HR.
  Qed.
End InitInverse.
Print Assumptions stored_success_identity.
Print Assumptions paid_success_identity.
Print Assumptions successful_initialization_extracts_identity_and_tail.
