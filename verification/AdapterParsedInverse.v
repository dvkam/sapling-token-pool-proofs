From Coq Require Import List String Ascii ZArith.
Require Import FullVM_WIP AdapterRoute AdapterAuthorization SourceLink.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(* Complete adapter code terms are bound to pinned parsed sources; the
   parser/translator, primitive correspondence and ticket validity are trusted. *)
Section Authorization.
  Variable prim : string -> stack -> option stack.
  Variable attached : nat.
  Variable sender : value.
  Variable compare_value : value -> value -> Z.
  Variable pack_address : value -> list nat.
  Variable pool_lookup import_lookup : value -> option value.
  Variable operation : value -> value -> value.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez attached :: rest).
  Hypothesis sender_frame : forall rest, prim "SENDER" rest = Some (sender :: rest).
  Hypothesis compare_frame : forall left right rest,
    prim "COMPARE_value" (left :: right :: rest) = Some (VInt (compare_value left right) :: rest).
  Hypothesis compare_zero : forall left right, compare_value left right = 0 <-> left = right.
  Hypothesis pack_frame : forall address rest,
    prim "PACK_address" (address :: rest) = Some (VBytes (pack_address address) :: rest).
  Hypothesis pool_frame : forall address rest,
    prim "CONTRACT_pool" (address :: rest) = Some (optional_handle (pool_lookup address) :: rest).
  Hypothesis import_frame : forall address rest,
    prim "CONTRACT_import" (address :: rest) = Some (optional_handle (import_lookup address) :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) = Some (operation parameter handle :: rest).

  Theorem parsed_ingress_requires_authorization_and_stored_route :
    forall ticketer payload quantity pool issuer contents proof used frame output,
    run prim 160 SourceLink.parsed_ingress_full
      (VPair (VTicket ticketer payload quantity)
        (VPair pool (VPair (VPair issuer contents) (VPair proof (VBool used)))) :: frame) = Some output ->
    attached = 0%nat /\ used = false /\ sender = issuer /\
    issuer = ticketer /\ contents = payload /\
    exists handle, pool_lookup pool = Some handle /\
      output = VPair
        (VList [operation (VPair (VSome (VTicket ticketer payload quantity)) (VList [proof])) handle])
        (VPair pool (VPair (VPair issuer contents) (VPair proof (VBool true)))) :: frame.
  Proof.
    intros ticketer payload quantity pool issuer contents proof used frame output H.
    rewrite SourceLink.ingress_full_source_matches in H.
    eapply AdapterAuthorization.successful_ingress_requires_authorization_and_stored_route; eauto.
  Qed.
  Theorem parsed_egress_requires_authorization_and_stored_route :
    forall ticketer payload quantity pool issuer contents beneficiary frame output,
    run prim 160 SourceLink.parsed_egress_full
      (VPair (VTicket ticketer payload quantity) (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame) = Some output ->
    attached = 0%nat /\ List.length (pack_address beneficiary) = 28%nat /\
    sender = pool /\ issuer = ticketer /\ contents = payload /\
    exists handle, import_lookup issuer = Some handle /\
      output = VPair
        (VList [operation (VList [VPair beneficiary (VList [VTicket ticketer payload quantity])]) handle])
        (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame.
  Proof.
    intros ticketer payload quantity pool issuer contents beneficiary frame output H.
    rewrite SourceLink.egress_full_source_matches in H.
    eapply AdapterAuthorization.successful_egress_requires_authorization_and_stored_route; eauto.
  Qed.
End Authorization.
Print Assumptions parsed_ingress_requires_authorization_and_stored_route.
Print Assumptions parsed_egress_requires_authorization_and_stored_route.
