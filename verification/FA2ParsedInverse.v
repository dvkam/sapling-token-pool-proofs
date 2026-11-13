From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2Boundary FA2Environment FA2MixedBatch FA2SenderMap
  FA2PrivateSuccess FA2PublicSuccess FA2OutputInverse SourceLink.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* SourceLink checks the complete parsed program equality; source importer
   and modeled/protocol primitive correspondence remain trusted. *)
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

  Theorem parsed_fa2_success_classifies_output :
    forall txs old token id frame output,
    run prim 139 SourceLink.parsed_fa2_full
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
    rewrite SourceLink.fa2_full_public_success_matches in HR.
    eapply FA2OutputInverse.successful_full_call_classifies_output; eauto.
  Qed.
End Classify.
Print Assumptions parsed_fa2_success_classifies_output.
