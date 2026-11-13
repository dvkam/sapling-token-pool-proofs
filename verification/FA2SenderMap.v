From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2DepositBody FA2MixedBatch FA2Environment FA2Combined.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* Concrete abstract map on the only reachable shapes. This does not prove
   Octez map semantics or justify non-sender updates. *)
Section SenderMap.
  Variable sender : value.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.

  Definition lookup (key map : value) : option nat :=
    match map with
    | VMap [(k,VNat n)] => if eq_value key k then Some n else None
    | _ => None end.
  Definition update (key : value) (new : option nat) (_map : value) : value :=
    match new with None => VMap [] | Some n => VMap [(key,VNat n)] end.
  Definition shape (map : value) : Prop :=
    map = VMap [] \/ exists n, map = VMap [(sender,VNat n)].
  Definition amount (map : value) : nat :=
    match map with VMap [(_,VNat n)] => n | _ => 0%nat end.

  Lemma sender_lookup : forall map, shape map ->
    FA2DepositBody.balance_or_zero (lookup sender map) = amount map.
  Proof.
    intros map [E|[n E]]; subst; cbn [lookup amount FA2DepositBody.balance_or_zero].
    - reflexivity.
    - destruct (eq_value sender sender); [reflexivity|contradiction].
  Qed.

  Inductive counted_trace
    (verify : value -> value -> option (value * Z * value))
    (unpack : value -> option value) (pack : value -> list nat) :
    list value -> value -> value -> list value -> value -> value -> list value -> nat -> Prop :=
  | counted_nil : forall state map ws, counted_trace verify unpack pack [] state map ws state map ws 0%nat
  | counted_positive : forall tx txs old map ws bound balance next recipient final finalmap finalws sum,
      verify tx old = Some (bound,balance,next) -> 0 < balance ->
      unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
      counted_trace verify unpack pack txs next map (VPair recipient (VNat (Z.to_nat balance)) :: ws) final finalmap finalws sum ->
      counted_trace verify unpack pack (tx::txs) old map ws final finalmap finalws sum
  | counted_negative : forall tx txs old map ws balance next final finalmap finalws sum,
      verify tx old = Some (VBytes [], balance, next) -> balance < 0 ->
      counted_trace verify unpack pack txs next
        (update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map)
        ws final finalmap finalws sum ->
      counted_trace verify unpack pack (tx::txs) old map ws final finalmap finalws
        ((Z.to_nat (Z.abs balance) + sum)%nat)
  | counted_zero : forall tx txs old map ws next final finalmap finalws sum,
      verify tx old = Some (VBytes [],0,next) ->
      counted_trace verify unpack pack txs next map ws final finalmap finalws sum ->
      counted_trace verify unpack pack (tx::txs) old map ws final finalmap finalws sum.

  Lemma counted_is_mixed : forall verify unpack pack txs old map ws final finalmap finalws sum,
    counted_trace verify unpack pack txs old map ws final finalmap finalws sum ->
    FA2MixedBatch.mixed_trace verify unpack pack sender lookup update txs old map ws final finalmap finalws.
  Proof.
    intros verify unpack pack txs old map ws final finalmap finalws sum H.
    induction H.
    - constructor.
    - eapply FA2MixedBatch.mixed_positive; eauto.
    - eapply FA2MixedBatch.mixed_negative; eauto.
    - eapply FA2MixedBatch.mixed_zero; eauto.
  Qed.

  Theorem reachable_sender_deposit_sum : forall verify unpack pack txs old map ws final finalmap finalws sum,
    counted_trace verify unpack pack txs old map ws final finalmap finalws sum ->
    shape map -> shape finalmap /\ amount finalmap = (amount map + sum)%nat.
  Proof.
    intros verify unpack pack txs old map ws final finalmap finalws sum H.
    induction H; intros HS.
    - split; [exact HS|lia].
    - now apply IHcounted_trace.
    - assert (HU : shape (update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map)).
      { right; eexists; reflexivity. }
      specialize (IHcounted_trace HU). destruct IHcounted_trace as [HF HE].
      split; [exact HF|].
      cbn [update amount] in HE.
      rewrite (sender_lookup map HS) in HE. lia.
    - now apply IHcounted_trace.
  Qed.

  Theorem successful_loop_and_sender_deposit_sum :
    forall verify unpack pack other txs old map ws final finalmap finalws sum frame,
    counted_trace verify unpack pack txs old map ws final finalmap finalws sum ->
    shape map ->
    run (FA2Environment.primitive verify unpack pack sender lookup update other) 129
      [Iter FA2Combined.canonical_iteration] (VList txs :: old :: map :: VList ws :: frame) =
      Some (final :: finalmap :: VList finalws :: frame) /\
    shape finalmap /\ amount finalmap = (amount map + sum)%nat.
  Proof.
    intros verify unpack pack other txs old map ws final finalmap finalws sum frame H HS.
    split.
    - eapply FA2MixedBatch.unbounded_successful_mixed_batch.
      eapply counted_is_mixed; exact H.
    - eapply reachable_sender_deposit_sum; eauto.
  Qed.
End SenderMap.
Print Assumptions reachable_sender_deposit_sum.
Print Assumptions successful_loop_and_sender_deposit_sum.
