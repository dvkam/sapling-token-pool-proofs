From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA12LoopBody FA12MixedBatch FA12Boundary FA12FullInverse SourceLink.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Parsed-source equality is kernel checked in SourceLink; the original
   Michelson parser/translation and modeled primitive meanings remain trusted. *)
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

  Theorem parsed_fa12_success_extracts_trace :
    forall txs old frame output,
    run prim 140 SourceLink.parsed_fa12_full
      (VPair (VList txs) (VPair old token) :: frame) = Some output ->
    amount = 0%nat /\
    exists handle final finalds finalws,
      contract_lookup token = Some handle /\
      FA12MixedBatch.mixed_trace verify unpack pack self sender handle operation
        txs old [] [] final finalds finalws /\
      output = VPair (VList (rev finalds ++ rev finalws)) (VPair final token) :: frame.
  Proof.
    intros txs old frame output H.
    rewrite SourceLink.fa12_full_matches in H.
    eapply FA12FullInverse.successful_full_call_extracts_trace; eauto.
  Qed.
End Inverse.
Print Assumptions parsed_fa12_success_extracts_trace.
