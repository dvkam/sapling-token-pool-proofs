From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2Boundary FA2Combined FA2Environment FA2MixedBatch
  FA2PrivateSuccess FA2PublicSuccess FA2SenderMap FA2StepInverse FA2FullExtract FA2TraceShape.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Successful full-call converse for the concrete reachable single-sender map
   dispatcher. The input is a typed-shape VM value. Bound bytes, address
   encoding, map/protocol refinement, token semantics and atomicity are not
   established by this theorem. *)
Section Inverse.
  Variable sender : value.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable other : string -> stack -> option stack.
  Variable amount : nat.
  Let lookup := FA2SenderMap.lookup eq_value.
  Let update := FA2SenderMap.update.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez amount :: rest).
  Hypothesis verify_bound_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.

  Local Opaque run.

  Theorem successful_full_extracts_reachable_trace :
    forall txs old token id frame output,
    run prim 139 FA2PublicSuccess.full_code
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) = Some output ->
    amount = 0%nat /\
    exists final finalmap finalws sum withdrawals,
      FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
        txs old (VMap []) [] final finalmap finalws /\
      FA2SenderMap.counted_trace sender eq_value verify unpack pack
        txs old (VMap []) [] final finalmap finalws sum /\
      FA2SenderMap.shape sender finalmap /\ FA2SenderMap.amount finalmap = sum /\
      finalws = FA2PublicSuccess.pair_entries (rev withdrawals) /\
      run prim 128 (FA2Boundary.private_post FA2PublicSuccess.public_code)
        (final :: finalmap :: VList finalws :: token :: id :: frame) = Some output.
  Proof.
    intros txs old token id frame output H.
    unfold FA2PublicSuccess.full_code in H.
    destruct (FA2FullExtract.successful_full_call_extracts_loop prim amount amount_frame
      FA2PublicSuccess.public_code txs old token id frame output H)
      as [HA [middle [HI HP]]].
    split; [exact HA|].
    assert (EXTRACT : exists final finalmap finalws,
      middle = final :: finalmap :: VList finalws :: token :: id :: frame /\
      FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
        txs old (VMap []) [] final finalmap finalws).
    { eapply FA2StepInverse.successful_loop_extracts_trace; eauto. }
    destruct EXTRACT as [final [finalmap [finalws [E HT]]]]; subst middle.
    destruct (FA2TraceShape.reachable_trace_shape_and_count sender eq_value verify unpack pack
      txs old final finalmap finalws HT) as [sum [withdrawals [HC [HS [Hsum Hws]]]]].
    exists final, finalmap, finalws, sum, withdrawals. repeat split; auto.
  Qed.
End Inverse.
Print Assumptions successful_full_extracts_reachable_trace.
