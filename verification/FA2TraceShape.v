From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2MixedBatch FA2SenderMap FA2PublicSuccess.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* Reachable concrete map and withdrawal shapes, derived from a trace rather
   than supplied as a postcondition. Octez map refinement remains external. *)
Section Shape.
  Variable sender : value.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Let lookup := FA2SenderMap.lookup eq_value.
  Let update := FA2SenderMap.update.

  Lemma mixed_has_count : forall txs old map ws final finalmap finalws,
    FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
      txs old map ws final finalmap finalws ->
    exists sum, FA2SenderMap.counted_trace sender eq_value verify unpack pack
      txs old map ws final finalmap finalws sum.
  Proof.
    intros txs old map ws final finalmap finalws H.
    induction H.
    - exists 0%nat. constructor.
    - destruct IHmixed_trace as [sum HC]. exists sum. eapply FA2SenderMap.counted_positive; eauto.
    - destruct IHmixed_trace as [sum HC]. exists (Z.to_nat (Z.abs balance) + sum)%nat.
      eapply FA2SenderMap.counted_negative; eauto.
    - destruct IHmixed_trace as [sum HC]. exists sum. eapply FA2SenderMap.counted_zero; eauto.
  Qed.

  Definition withdrawal_shape (ws : list value) : Prop :=
    exists pairs : list (value * value), ws = FA2PublicSuccess.pair_entries pairs.

  Lemma positive_preserves_shape : forall ws recipient amount,
    withdrawal_shape ws -> withdrawal_shape (VPair recipient (VNat amount) :: ws).
  Proof.
    intros ws recipient amount [pairs E]. subst.
    exists ((recipient,VNat amount)::pairs). reflexivity.
  Qed.

  Lemma mixed_preserves_withdrawal_shape : forall txs old map ws final finalmap finalws,
    FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
      txs old map ws final finalmap finalws ->
    withdrawal_shape ws -> withdrawal_shape finalws.
  Proof.
    intros txs old map ws final finalmap finalws H.
    induction H; intros HS; auto.
    apply IHmixed_trace. now apply positive_preserves_shape.
  Qed.

  Theorem reachable_trace_shape_and_count : forall txs old final finalmap finalws,
    FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
      txs old (VMap []) [] final finalmap finalws ->
    exists sum withdrawals,
      FA2SenderMap.counted_trace sender eq_value verify unpack pack
        txs old (VMap []) [] final finalmap finalws sum /\
      FA2SenderMap.shape sender finalmap /\ FA2SenderMap.amount finalmap = sum /\
      finalws = FA2PublicSuccess.pair_entries (rev withdrawals).
  Proof.
    intros txs old final finalmap finalws HT.
    destruct (mixed_has_count _ _ _ _ _ _ _ HT) as [sum HC].
    assert (HM : FA2SenderMap.shape sender finalmap /\
      FA2SenderMap.amount finalmap = (FA2SenderMap.amount (VMap []) + sum)%nat).
    { eapply FA2SenderMap.reachable_sender_deposit_sum; eauto.
      left. reflexivity. }
    assert (HW : withdrawal_shape finalws).
    { eapply mixed_preserves_withdrawal_shape; eauto.
      exists []. reflexivity. }
    destruct HW as [pairs E]. exists sum, (rev pairs).
    rewrite rev_involutive. destruct HM as [HS HA]. repeat split; auto.
  Qed.
End Shape.
