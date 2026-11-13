(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA12LoopBody FA12MixedBatch FA12Boundary FA12FullInverse SourceLink.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Parsed-source equality is kernel checked in SourceLink; the original
   Michelson parser/translation and modeled primitive meanings remain trusted. *)
Require Import AssetLedger SaplingNotes PoolCollateral CollateralCallTree FA12ParsedInverse.
Section ParsedCollateral.
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


  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable decode_call : value -> option (value * value).
  Hypothesis operation_fields : forall parameter target,
    decode_call (operation parameter target) = Some (target,parameter).
  Hypothesis sender_other : sender <> self.
  Variable represents : value -> list note -> Prop.
  Hypothesis note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists nextnotes, represents next nextnotes /\ note_transition notes nextnotes balance.
  Hypothesis represented_liability_unique : forall state a b,
    represents state a -> represents state b -> liability a = liability b.

  (* This starts from success of the WHOLE parsed modeled call, not a supplied
     trace or output shape. SourceLink's translator and all primitive/context
     specifications remain external to actual Octez correspondence. *)
  Theorem whole_parsed_fa12_success_produces_source_certificate :
    forall txs old frame output oldnotes,
    run prim 140 SourceLink.parsed_fa12_full
      (VPair (VList txs) (VPair old token) :: frame) = Some output ->
    represents old oldnotes ->
    amount = 0%nat /\ exists handle final emitted transfers newnotes,
      contract_lookup token = Some handle /\
      output = VPair (VList emitted) (VPair final token) :: frame /\
      represents final newnotes /\
      decode_fa12_operations eq_value decode_call handle emitted = Some transfers /\
      source_entry_certificate eq_value self oldnotes newnotes emitted transfers /\
      liability newnotes - liability oldnotes <= net_delta eq_value self transfers /\
      (forall before : ledger, liability oldnotes <= before self ->
        liability newnotes <= settle eq_value transfers before self).
  Proof.
    intros txs old frame output oldnotes RUN REPR.
    assert (EXTRACT : amount = 0%nat /\ exists handle final ds ws,
      contract_lookup token = Some handle /\
      FA12MixedBatch.mixed_trace verify unpack pack self sender handle operation
        txs old [] [] final ds ws /\
      output = VPair (VList (rev ds ++ rev ws)) (VPair final token) :: frame).
    { eapply FA12ParsedInverse.parsed_fa12_success_extracts_trace; eauto. }
    destruct EXTRACT as [HA [handle [final [ds [ws [LOOKUP [TRACE OUTPUT]]]]]]].
    split; [exact HA|].
    destruct (fa12_emitted_operations_cover_liability_change eq_value verify unpack pack
      self sender handle operation decode_call operation_fields sender_other
      represents note_soundness txs old final ds ws oldnotes TRACE REPR)
      as [ns [ts [HR [DECODE MARGIN]]]].
    assert (CERT : source_entry_certificate eq_value self oldnotes ns (rev ds ++ rev ws) ts).
    { eapply fa12_source_entry; eauto. }
    exists handle,final,(rev ds ++ rev ws),ts,ns.
    split; [exact LOOKUP|]. split; [exact OUTPUT|]. split; [exact HR|].
    split; [exact DECODE|]. split; [exact CERT|]. split; [lia|].
    intros before BACKED. rewrite settlement_reserve_effect. lia.
  Qed.
End ParsedCollateral.
Print Assumptions whole_parsed_fa12_success_produces_source_certificate.
