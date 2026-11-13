(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String Bool Arith.
Require Import MichelineRaw MichelinePrograms MichelineRoundtrip.
Import ListNotations.
Open Scope string_scope.

(* Syntactic evidence only. Native entrypoint resolution, deployed code
   identity and operation provenance remain separate platform obligations. *)
Definition parameter (p : node) : option node :=
  match p with
  | MSeq (MPrim "parameter" [arg] _ :: _) => Some arg
  | MSeq (_ :: MPrim "parameter" [arg] _ :: _) => Some arg
  | _ => None end.
Definition has_named_field (field : string) (p : node) : bool :=
  existsb (fun tok => match tok with
     | TPrim _ _ anns => existsb (String.eqb field) anns
     | _ => false end) (encode p).
Definition no_named_parameter (field : string) (p : node) : bool :=
  match parameter p with Some arg => negb (has_named_field field arg) | None => false end.
Definition contract_at (ts : list token) (i : nat) : option node :=
  match decode 128 (skipn i ts) with
  | Some (MPrim "CONTRACT" args ann, _) => Some (MPrim "CONTRACT" args ann)
  | _ => None end.
Definition ticket_contents := MPrim "pair" [MPrim "nat" [] []; MPrim "option" [MPrim "bytes" [] []] []] [].
Definition ticket_type := MPrim "ticket" [ticket_contents] [].
Definition sapling_list := MPrim "list" [MPrim "sapling_transaction" [MInt "8"] []] [].
Definition count_prim (name : string) (ts : list token) : nat :=
  List.length (filter (fun t => match t with TPrim p _ _ => String.eqb p name | _ => false end) ts).

Example five_sources_each_have_one_contract_lookup :
  count_prim "CONTRACT" fa12_tokens = 1 /\ count_prim "CONTRACT" fa2_tokens = 1 /\
  count_prim "CONTRACT" ticket_tokens = 1 /\ count_prim "CONTRACT" ingress_tokens = 1 /\
  count_prim "CONTRACT" egress_tokens = 1.
Proof. vm_compute. repeat split; reflexivity. Qed.
Example pools_only_construct_token_transfers_in_source :
  count_prim "TRANSFER_TOKENS" fa12_tokens = 2 /\ count_prim "TRANSFER_TOKENS" fa2_tokens = 1 /\
  count_prim "TRANSFER_TOKENS" ticket_tokens = 1 /\
  count_prim "CREATE_CONTRACT" fa12_tokens = 0 /\ count_prim "CREATE_CONTRACT" fa2_tokens = 0 /\
  count_prim "CREATE_CONTRACT" ticket_tokens = 0 /\
  count_prim "SET_DELEGATE" fa12_tokens = 0 /\ count_prim "SET_DELEGATE" fa2_tokens = 0 /\
  count_prim "SET_DELEGATE" ticket_tokens = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example fa12_parameter_has_no_transfer_entrypoint : no_named_parameter "%transfer" fa12_expected = true.
Proof. vm_compute. reflexivity. Qed.
Example fa2_parameter_has_no_transfer_entrypoint : no_named_parameter "%transfer" fa2_expected = true.
Proof. vm_compute. reflexivity. Qed.
Example fa_pools_both_accept_sapling_transaction_list :
  parameter fa12_expected = Some sapling_list /\ parameter fa2_expected = Some sapling_list.
Proof. vm_compute. split; reflexivity. Qed.
Example egress_parameter_has_no_import_ticket_entrypoint : no_named_parameter "%import_ticket" egress_expected = true.
Proof. vm_compute. reflexivity. Qed.
Example ticket_parameter_is_pair_not_ticket :
  parameter ticket_expected = Some (MPrim "pair" [
    MPrim "option" [ticket_type] ["%paid_ticket"]; sapling_list] []) /\
  parameter ticket_expected <> Some ticket_type.
Proof. vm_compute. split; congruence. Qed.
Example ingress_parameter_is_ticket : parameter ingress_expected = Some ticket_type.
Proof. vm_compute. reflexivity. Qed.

Example fa12_lookup_has_transfer_entrypoint :
 contract_at fa12_tokens 35 = Some (MPrim "CONTRACT" [MPrim "pair" [
   MPrim "address" [] [];MPrim "address" [] [];MPrim "nat" [] []] []] ["%transfer"]).
Proof. vm_compute. reflexivity. Qed.
Example fa2_lookup_has_transfer_entrypoint :
 match contract_at fa2_tokens 152 with
 | Some (MPrim "CONTRACT" [_] ["%transfer"]) => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.
Example ticket_payout_lookup_is_default_ticket :
 contract_at ticket_tokens 148 = Some (MPrim "CONTRACT" [ticket_type] []).
Proof. vm_compute. reflexivity. Qed.
Example ingress_pool_lookup_requires_pair_not_ticket :
 contract_at ingress_tokens 94 = Some (MPrim "CONTRACT" [MPrim "pair"
   [MPrim "option" [ticket_type] []; sapling_list] []] []).
Proof. vm_compute. reflexivity. Qed.
Example egress_lookup_has_import_ticket_entrypoint :
 match contract_at egress_tokens 113 with
 | Some (MPrim "CONTRACT" [_] ["%import_ticket"]) => true | _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

(* A deliberately scoped resolver model for the five unannotated non-or
   parameter roots above. None represents default, Some name a named entrypoint.
   Octez resolver/type-equivalence/contract-address correspondence is an
   explicit unproved platform bridge; this is NOT OCaml refinement. *)
Definition combined_entrypoint (address_annot instruction_annot : option string)
    : option (option string) :=
  match address_annot,instruction_annot with
  | None,None => Some None
  | None,Some x | Some x,None => Some (Some x)
  | Some _,Some _ => None
  end.
Definition simple_self_resolver (param expected : node)
    (address_annot instruction_annot : option string) : bool :=
  match combined_entrypoint address_annot instruction_annot with
  | Some None => if node_eq_dec param expected then true else false
  | _ => false
  end.

Theorem annotated_transfer_fails_in_nameless_interface_model :
  forall param expected address_entrypoint,
  simple_self_resolver param expected address_entrypoint (Some "transfer") = false.
Proof. intros param expected [name|]; reflexivity. Qed.
Theorem nonmatching_ticket_fails_in_nameless_interface_model :
  forall param address_entrypoint,
  param <> ticket_type -> simple_self_resolver param ticket_type address_entrypoint None = false.
Proof.
  intros param [name|] H; [reflexivity|]. unfold simple_self_resolver, combined_entrypoint.
  destruct (node_eq_dec param ticket_type); [contradiction|reflexivity].
Qed.
Example ticket_source_shape_fails_in_nameless_interface_model :
  forall address_entrypoint,
  match parameter ticket_expected with
  | Some param => simple_self_resolver param ticket_type address_entrypoint None = false
  | None => False end.
Proof.
  intros. change (simple_self_resolver (MPrim "pair" [MPrim "option" [ticket_type] ["%paid_ticket"];sapling_list] []) ticket_type address_entrypoint None = false).
  apply nonmatching_ticket_fails_in_nameless_interface_model. discriminate.
Qed.
Print Assumptions annotated_transfer_fails_in_nameless_interface_model.
Print Assumptions ticket_source_shape_fails_in_nameless_interface_model.
