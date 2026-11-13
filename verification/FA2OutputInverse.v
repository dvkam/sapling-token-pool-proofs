From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2Boundary FA2Environment FA2MixedBatch FA2SenderMap
  FA2PrivateSuccess FA2PublicSuccess FA2FullInverse.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Classifies every successful modeled call under complete framed primitive
   specifications and the concrete reachable single-sender map model. No
   successful trace or output classification is a premise. *)
Section Classify.
  Variable sender : value.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable other : string -> stack -> option stack.
  Variable amount : nat.
  Variable pool : value.
  Variable operation : value -> value -> value.
  Variable contract_lookup : value -> option value.
  Let lookup := FA2SenderMap.lookup eq_value.
  Let update := FA2SenderMap.update.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez amount :: rest).
  Hypothesis verify_bound_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (pool :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) =
      Some (operation parameter handle :: rest).
  Hypothesis contract_frame : forall token rest,
    prim "CONTRACT_FA2_TRANSFER" (token :: rest) =
      Some ((match contract_lookup token with None => VNone | Some handle => VSome handle end) :: rest).

  Lemma lookup_none_rejects : forall fuel state entries ws token id frame,
    run prim (4 + fuel)%nat FA2PublicSuccess.public_after_lookup
      (VNone :: state :: VMap entries :: VList ws :: token :: id :: frame) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.

  Theorem successful_full_call_classifies_output :
    forall txs old token id frame output,
    run prim 139 FA2PublicSuccess.full_code
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) = Some output ->
    amount = 0%nat /\
    exists final entries withdrawals sum,
      FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
        txs old (VMap []) [] final (VMap entries)
          (FA2PublicSuccess.pair_entries (rev withdrawals)) /\
      FA2SenderMap.shape sender (VMap entries) /\ FA2SenderMap.amount (VMap entries) = sum /\
      FA2SenderMap.counted_trace sender eq_value verify unpack pack
        txs old (VMap []) [] final (VMap entries)
          (FA2PublicSuccess.pair_entries (rev withdrawals)) sum /\
      ((entries = [] /\ withdrawals = [] /\
        output = VPair (VList []) (VPair final (VPair token id)) :: frame) \/
       ((List.length entries + List.length withdrawals <> 0)%nat /\
        exists handle, contract_lookup token = Some handle /\
        output = VPair (VList [operation (VList (FA2PublicSuccess.transfer_groups pool id entries withdrawals)) handle])
          (VPair final (VPair token id)) :: frame)).
  Proof.
    intros txs old token id frame output HR.
    destruct (FA2FullInverse.successful_full_extracts_reachable_trace sender eq_value verify unpack pack other amount
      amount_frame verify_bound_bytes txs old token id frame output HR)
      as [HA [final [finalmap [finalws [sum [withdrawals [HT [HC [HS [Hsum [Hws HP]]]]]]]]]]].
    assert (EM : exists entries, finalmap = VMap entries).
    { destruct HS as [E|[n E]]; [exists [] | exists [(sender,VNat n)]]; exact E. }
    destruct EM as [entries EM]. subst finalmap. subst finalws.
    split; [exact HA|].
    exists final, entries, withdrawals, sum.
    split; [exact HT|]. split; [exact HS|]. split; [exact Hsum|]. split; [exact HC|].
    destruct (Nat.eq_dec (List.length entries + List.length withdrawals) 0) as [HZ|HN].
    - assert (E : entries = [] /\ withdrawals = []).
      { destruct entries, withdrawals; cbn in HZ; try lia; auto. }
      destruct E as [E1 E2]; subst entries; subst withdrawals.
      left. repeat split; auto.
      rewrite (FA2PrivateSuccess.private_post_fuel prim 104) in HP.
      inversion HP; reflexivity.
    - right. split; [exact HN|].
      assert (Hnon : (List.length (FA2PublicSuccess.pair_entries (rev withdrawals)) + List.length entries <> 0)%nat).
      { unfold FA2PublicSuccess.pair_entries. rewrite map_length, rev_length. lia. }
      change (run prim 128 (FA2Boundary.private_post FA2PublicSuccess.public_code)
        (final :: VMap entries :: VList (FA2PublicSuccess.pair_entries (rev withdrawals)) :: token :: id :: frame) = Some output) in HP.
      pose proof HP as HP0.
      rewrite (FA2PublicSuccess.nonempty_post_selects_public prim final entries
        (FA2PublicSuccess.pair_entries (rev withdrawals)) token id frame Hnon) in HP.
      rewrite (FA2PublicSuccess.lookup_prefix prim 117), contract_frame in HP.
      destruct (contract_lookup token) as [handle|] eqn:HL.
      + exists handle. split; [reflexivity|].
        assert (Hcontract : forall rest, prim "CONTRACT_FA2_TRANSFER" (token :: rest) = Some (VSome handle :: rest)).
        { intros; rewrite contract_frame, HL; reflexivity. }
        assert (HO : run prim 119 FA2PublicSuccess.public_code
          (final :: VMap entries :: VList (FA2PublicSuccess.pair_entries (rev withdrawals)) :: token :: id :: frame) =
          Some (VPair (VList [operation (VList (FA2PublicSuccess.transfer_groups pool id entries withdrawals)) handle])
            (VPair final (VPair token id)) :: frame)).
        { eapply FA2PublicSuccess.public_arm_constructs_ordered_transfer; eauto. }
        pose proof (FA2PublicSuccess.nonempty_post_selects_public prim final entries
          (FA2PublicSuccess.pair_entries (rev withdrawals)) token id frame Hnon) as SELECT.
        rewrite SELECT, HO in HP0. inversion HP0; reflexivity.
      + rewrite (lookup_none_rejects 113) in HP. discriminate.
  Qed.
End Classify.
Print Assumptions successful_full_call_classifies_output.
