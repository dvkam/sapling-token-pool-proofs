From Coq Require Import List String ZArith.
Require Import FullVM_WIP FA12LoopBody LoopInduction.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Successful batches only. Callback equations and source/Octez refinement
   are external premises; operations are constructed, not executed. *)
Inductive mixed_trace
  (verify : value -> value -> option (value * Z * value))
  (unpack : value -> option value) (pack : value -> list nat)
  (self sender handle : value) (operation : value -> value -> value) :
  list value -> value -> list value -> list value -> value -> list value -> list value -> Prop :=
| mixed_nil : forall state ds ws, mixed_trace verify unpack pack self sender handle operation [] state ds ws state ds ws
| mixed_positive : forall tx txs old ds ws bound balance next recipient final finalds finalws,
    verify tx old = Some (bound, balance, next) -> 0 < balance ->
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    mixed_trace verify unpack pack self sender handle operation txs next ds
      (operation (VPair self (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws)
      final finalds finalws ->
    mixed_trace verify unpack pack self sender handle operation (tx :: txs) old ds ws final finalds finalws
| mixed_negative : forall tx txs old ds ws balance next final finalds finalws,
    verify tx old = Some (VBytes [], balance, next) -> balance < 0 ->
    mixed_trace verify unpack pack self sender handle operation txs next
      (operation (VPair sender (VPair self (VNat (Z.to_nat (Z.abs balance))))) handle :: ds)
      ws final finalds finalws ->
    mixed_trace verify unpack pack self sender handle operation (tx :: txs) old ds ws final finalds finalws
| mixed_zero : forall tx txs old ds ws next final finalds finalws,
    verify tx old = Some (VBytes [], 0, next) ->
    mixed_trace verify unpack pack self sender handle operation txs next ds ws final finalds finalws ->
    mixed_trace verify unpack pack self sender handle operation (tx :: txs) old ds ws final finalds finalws.

Section Batch.
  Variable primitive : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable self sender : value.
  Variable operation : value -> value -> value.
  Hypothesis verify_frame : forall tx old bound balance next rest,
    verify tx old = Some (bound,balance,next) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis unpack_frame : forall bound recipient rest,
    unpack bound = Some recipient ->
    primitive "UNPACK_address" (bound :: rest) = Some (VSome recipient :: rest).
  Hypothesis pack_frame : forall recipient rest,
    primitive "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).
  Hypothesis self_frame : forall rest, primitive "SELF_ADDRESS" rest = Some (self :: rest).
  Hypothesis sender_frame : forall rest, primitive "SENDER" rest = Some (sender :: rest).
  Hypothesis operation_frame : forall parameters handle rest,
    primitive "TRANSFER_TOKENS" (parameters :: VMutez 0 :: handle :: rest) =
    Some (operation parameters handle :: rest).

  Lemma mixed_trace_iterates : forall txs initial ds ws final finalds finalws handle token,
    mixed_trace verify unpack pack self sender handle operation txs initial ds ws final finalds finalws ->
    forall frame,
    iterate (fun tx st => run primitive 128 FA12LoopBody.iteration (tx :: st))
      txs (initial :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (final :: handle :: token :: VPair (VList finalds) (VList finalws) :: frame).
  Proof.
    intros txs initial ds ws final finalds finalws handle token H.
    induction H; intros frame; cbn [iterate fold_left].
    - reflexivity.
    - assert (STEP : run primitive 128 FA12LoopBody.iteration
        (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
        Some (next :: handle :: token :: VPair (VList ds)
          (VList (operation (VPair self (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws)) :: frame)).
      { eapply FA12LoopBody.verified_positive_iteration_128; eauto. }
      rewrite STEP. now apply IHmixed_trace.
    - assert (STEP : run primitive 128 FA12LoopBody.iteration
        (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
        Some (next :: handle :: token :: VPair
          (VList (operation (VPair sender (VPair self (VNat (Z.to_nat (Z.abs balance))))) handle :: ds))
          (VList ws) :: frame)).
      { eapply FA12LoopBody.verified_negative_iteration_128; eauto. }
      rewrite STEP. now apply IHmixed_trace.
    - assert (STEP : run primitive 128 FA12LoopBody.iteration
        (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
        Some (next :: handle :: token :: VPair (VList ds) (VList ws) :: frame)).
      { eapply FA12LoopBody.verified_zero_iteration_128; eauto. }
      rewrite STEP. now apply IHmixed_trace.
  Qed.

  Theorem unbounded_successful_mixed_batch : forall txs initial ds ws final finalds finalws handle token,
    mixed_trace verify unpack pack self sender handle operation txs initial ds ws final finalds finalws ->
    forall frame,
    run primitive 129 [Iter FA12LoopBody.iteration]
      (VList txs :: initial :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (final :: handle :: token :: VPair (VList finalds) (VList finalws) :: frame).
  Proof.
    intros txs initial ds ws final finalds finalws handle token H frame.
    rewrite (LoopInduction.source_loop_unbounded primitive FA12LoopBody.iteration
      (fun tx st => run primitive 128 FA12LoopBody.iteration (tx :: st)) 127)
      by reflexivity.
    now apply mixed_trace_iterates.
  Qed.
End Batch.
Print Assumptions unbounded_successful_mixed_batch.
