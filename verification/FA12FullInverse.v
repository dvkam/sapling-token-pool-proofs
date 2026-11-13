From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA12LoopBody FA12MixedBatch FA12LoopExtract
  FA12AddressGuardInverse FA12StepInverse FA12Boundary.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Converse for the exact source-shaped FA1.2 whole program on a typed input
   stack. Callback frame equations are complete for both successful and failed
   verify/unpack/lookup outcomes; no callback assumes the existence of a trace.
   Source translation, protocol semantics, typing and actual execution of
   deferred operations remain outside this theorem. *)
Section Inverse.
  Variable prim : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable self sender token : value.
  Variable operation : value -> value -> value.
  Hypothesis verify_some : forall tx old bound balance next rest,
    verify tx old = Some (bound,balance,next) ->
    prim "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
      Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis verify_none : forall tx old rest,
    verify tx old = None ->
    prim "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) = Some (VNone :: rest).
  Hypothesis verify_bound_bytes : forall tx old bound balance next,
    verify tx old = Some (bound,balance,next) -> exists bytes, bound = VBytes bytes.
  Hypothesis unpack_some : forall bound recipient rest,
    unpack bound = Some recipient ->
    prim "UNPACK_address" (bound :: rest) = Some (VSome recipient :: rest).
  Hypothesis unpack_none : forall bound rest,
    unpack bound = None -> prim "UNPACK_address" (bound :: rest) = Some (VNone :: rest).
  Hypothesis pack_frame : forall recipient rest,
    prim "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (self :: rest).
  Hypothesis sender_frame : forall rest, prim "SENDER" rest = Some (sender :: rest).
  Hypothesis operation_frame : forall parameters handle0 rest,
    prim "TRANSFER_TOKENS" (parameters :: VMutez 0 :: handle0 :: rest) =
    Some (operation parameters handle0 :: rest).


  Variable amount : nat.
  Variable contract_lookup : value -> option value.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez amount :: rest).
  Hypothesis contract_frame : forall token0 rest,
    prim "CONTRACT_FA12_TRANSFER" (token0 :: rest) =
    Some (FA12Boundary.option_contract (contract_lookup token0) :: rest).

  Local Opaque run.

  Theorem successful_full_call_extracts_trace :
    forall txs old frame output,
    run prim 140 FA12Boundary.full_code
      (VPair (VList txs) (VPair old token) :: frame) = Some output ->
    amount = 0%nat /\
    exists handle final finalds finalws,
      contract_lookup token = Some handle /\
      FA12MixedBatch.mixed_trace verify unpack pack self sender handle operation
        txs old [] [] final finalds finalws /\
      output = VPair (VList (rev finalds ++ rev finalws)) (VPair final token) :: frame.
  Proof.
    intros txs old frame output H.
    unfold FA12Boundary.full_code in H.
    rewrite (FA12Boundary.init_amount_step prim 135), amount_frame in H.
    destruct amount as [|n].
    2: { rewrite (FA12Boundary.nonzero_amount_step prim 127 n) in H. discriminate. }
    split; [reflexivity|].
    rewrite (FA12Boundary.init_lookup_step prim 128) in H.
    destruct (contract_lookup token) as [handle|] eqn:HC.
    2: { rewrite (FA12Boundary.lookup_rejects prim contract_lookup contract_frame 123 token) in H by exact HC.
         discriminate. }
    rewrite (FA12Boundary.lookup_passes prim contract_lookup contract_frame 124 token handle) in H by exact HC.
    rewrite (FA12Boundary.loop_prefix_step prim 128) in H.
    destruct (iterate (fun tx st => run prim 128 iteration (tx :: st)) txs
      (old :: handle :: token :: VPair (VList []) (VList []) :: frame)) as [result|] eqn:HI;
      [|discriminate].
    assert (EXTRACT : exists final finalds finalws,
      result = final :: handle :: token :: VPair (VList finalds) (VList finalws) :: frame /\
      FA12MixedBatch.mixed_trace verify unpack pack self sender handle operation
        txs old [] [] final finalds finalws).
    { eapply FA12StepInverse.successful_loop_extracts_trace; eauto. }
    destruct EXTRACT as [final [finalds [finalws [ER HT]]]]. subst result.
    assert (Hfinal : run prim 128 FA12Boundary.final_code
      (final :: handle :: token :: VPair (VList finalds) (VList finalws) :: frame) =
      Some (VPair (VList (rev finalds ++ rev finalws)) (VPair final token) :: frame)).
    { pose proof (FA12Boundary.final_code_exact prim 114 final handle token (rev finalds) (rev finalws) frame) as HF.
      now rewrite !rev_involutive in HF. }
    rewrite Hfinal in H. inversion H; subst output.
    exists handle, final, finalds, finalws. repeat split; auto.
  Qed.
End Inverse.
Print Assumptions successful_full_call_extracts_trace.
