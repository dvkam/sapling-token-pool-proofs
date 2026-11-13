(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String Arith Bool.
Require Import MichelineRaw MichelinePrograms TypeInferenceWIP.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition fa2_item_type := MPrim "pair" [bare "address";bare "nat";bare "nat"] [].
Definition fa2_group_type := pair_type (bare "address") (unary_type "list" fa2_item_type).
Definition fa2_transfer_type := unary_type "list" fa2_group_type.
Definition fa2_entry_type := pair_type (bare "address") (bare "nat").
Definition ingress_argument := pair_type (unary_type "option" ticket_type) (unary_type "list" transaction8).
Definition import_argument := unary_type "list" (pair_type (bare "address") (unary_type "list" ticket_type)).

(* Explicit, source-specialized typing rules. The existing inference function
   is used only by proof automation to choose intermediate stack witnesses.
   No rule accepts an inference result as a typing premise. This is not yet
   proved equivalent to Octez's native typing or execution. *)
Inductive dseq : list node -> list node -> option (list node) -> Prop :=
| DEnd : forall s, dseq [] s (Some s)
| DNext : forall i code s mid out, done i s (Some mid) -> dseq code mid out -> dseq (i::code) s out
| DFail : forall i s, done i s None -> dseq [i] s None
with done : node -> list node -> option (list node) -> Prop :=
| DNil : forall s, done (MPrim "NIL" [bare "operation"] []) s (Some (list_operation::s))
| DNilFA2Entry : forall s, done (MPrim "NIL" [fa2_entry_type] []) s (Some (unary_type "list" fa2_entry_type::s))
| DNilFA2Group : forall s, done (MPrim "NIL" [fa2_group_type] []) s (Some (unary_type "list" fa2_group_type::s))
| DNilFA2Item : forall s, done (MPrim "NIL" [fa2_item_type] []) s (Some (unary_type "list" fa2_item_type::s))
| DNilTransaction : forall s, done (MPrim "NIL" [transaction8] []) s (Some (unary_type "list" transaction8::s))
| DNilTicket : forall s, done (MPrim "NIL" [ticket_type] []) s (Some (unary_type "list" ticket_type::s))
| DNilImport : forall s, done (MPrim "NIL" [pair_type (bare "address") (unary_type "list" ticket_type)] []) s (Some (unary_type "list" (pair_type (bare "address") (unary_type "list" ticket_type))::s))
| DPair : forall a b s, done (MPrim "PAIR" [] []) (a::b::s) (Some (pair_type a b::s))
| DPair3 : forall a b c s, done (MPrim "PAIR" [MInt "3"] []) (a::b::c::s) (Some (pair_type a (pair_type b c)::s))
| DPair4 : forall a b c d s, done (MPrim "PAIR" [MInt "4"] []) (a::b::c::d::s) (Some (pair_type a (pair_type b (pair_type c d))::s))
| DSwap : forall a b s, done (MPrim "SWAP" [] []) (a::b::s) (Some (b::a::s))
| DAmount : forall s, done (MPrim "AMOUNT" [] []) s (Some (bare "mutez"::s))
| DPushMutez : forall s, done (MPrim "PUSH" [bare "mutez";MInt "0"] []) s (Some (bare "mutez"::s))
| DPushNat0 : forall s, done (MPrim "PUSH" [bare "nat";MInt "0"] []) s (Some (bare "nat"::s))
| DPushNat28 : forall s, done (MPrim "PUSH" [bare "nat";MInt "28"] []) s (Some (bare "nat"::s))
| DPushFail : forall s, done (MPrim "PUSH" [bare "string";MString "FA_NON_DEFAULT_RECIPIENT"] []) s (Some (bare "string"::s))
| DPushString : forall text s, done (MPrim "PUSH" [bare "string";MString text] []) s (Some (bare "string"::s))
| DPushTrue : forall s, done (MPrim "PUSH" [bare "bool"; MPrim "True" [] []] []) s (Some (bare "bool"::s))
| DCompareNat : forall s, done (MPrim "COMPARE" [] []) (bare "nat"::bare "nat"::s) (Some (bare "int"::s))
| DCompareMutez : forall s, done (MPrim "COMPARE" [] []) (bare "mutez"::bare "mutez"::s) (Some (bare "int"::s))
| DCompareAddress : forall s, done (MPrim "COMPARE" [] []) (bare "address"::bare "address"::s) (Some (bare "int"::s))
| DCompareTicketIdentity : forall s, done (MPrim "COMPARE" [] []) (ticket_identity_type::ticket_identity_type::s) (Some (bare "int"::s))
| DEq : forall s, done (MPrim "EQ" [] []) (bare "int"::s) (Some (bare "bool"::s))
| DGt : forall s, done (MPrim "GT" [] []) (bare "int"::s) (Some (bare "bool"::s))
| DLt : forall s, done (MPrim "LT" [] []) (bare "int"::s) (Some (bare "bool"::s))
| DAbs : forall s, done (MPrim "ABS" [] []) (bare "int"::s) (Some (bare "nat"::s))
| DUnit : forall s, done (MPrim "UNIT" [] []) s (Some (bare "unit"::s))
| DFailUnit : forall s, done (MPrim "FAILWITH" [] []) (bare "unit"::s) None
| DFailString : forall s, done (MPrim "FAILWITH" [] []) (bare "string"::s) None
| DUnpair : forall t a b s, unpair_type t = Some (a,b) -> done (MPrim "UNPAIR" [] []) (t::s) (Some (a::b::s))
| DUnpair3 : forall t a b c s, unpair_types 3 t = Some [a;b;c] -> done (MPrim "UNPAIR" [MInt "3"] []) (t::s) (Some (a::b::c::s))
| DUnpair4 : forall t a b c d s, unpair_types 4 t = Some [a;b;c;d] -> done (MPrim "UNPAIR" [MInt "4"] []) (t::s) (Some (a::b::c::d::s))
| DCar : forall t a b s, unpair_type t = Some (a,b) -> done (MPrim "CAR" [] []) (t::s) (Some (a::s))
| DCdr : forall t a b s, unpair_type t = Some (a,b) -> done (MPrim "CDR" [] []) (t::s) (Some (b::s))
| DDupAddress : forall s, done (MPrim "DUP" [] []) (bare "address"::s) (Some (bare "address"::bare "address"::s))
| DDupInt : forall s, done (MPrim "DUP" [] []) (bare "int"::s) (Some (bare "int"::bare "int"::s))
| DDupContract : forall s, done (MPrim "DUP" [] []) (unary_type "contract" fa12_transfer_type::s) (Some (unary_type "contract" fa12_transfer_type::unary_type "contract" fa12_transfer_type::s))
| DDupFA2Contract : forall s, done (MPrim "DUP" [] []) (unary_type "contract" fa2_transfer_type::s) (Some (unary_type "contract" fa2_transfer_type::unary_type "contract" fa2_transfer_type::s))
| DDupAny : forall t s, valid_type 64 t = true -> dupable 32 t = true -> done (MPrim "DUP" [] []) (t::s) (Some (t::t::s))
| DDupN : forall digit n t s, small_nat (MInt digit) = Some (S n) -> nth_error s n = Some t -> valid_type 64 t = true -> dupable 32 t = true -> done (MPrim "DUP" [MInt digit] []) s (Some (t::s))
| DDrop : forall a s, done (MPrim "DROP" [] []) (a::s) (Some s)
| DDrop2 : forall a b s, done (MPrim "DROP" [MInt "2"] []) (a::b::s) (Some s)
| DDig2 : forall a b c s, done (MPrim "DIG" [MInt "2"] []) (a::b::c::s) (Some (c::a::b::s))
| DDig3 : forall a b c d s, done (MPrim "DIG" [MInt "3"] []) (a::b::c::d::s) (Some (d::a::b::c::s))
| DDig4 : forall a b c d e s, done (MPrim "DIG" [MInt "4"] []) (a::b::c::d::e::s) (Some (e::a::b::c::d::s))
| DDig5 : forall a b c d e f s, done (MPrim "DIG" [MInt "5"] []) (a::b::c::d::e::f::s) (Some (f::a::b::c::d::e::s))
| DDug2 : forall a b c s, done (MPrim "DUG" [MInt "2"] []) (a::b::c::s) (Some (b::c::a::s))
| DDug3 : forall a b c d s, done (MPrim "DUG" [MInt "3"] []) (a::b::c::d::s) (Some (b::c::d::a::s))
| DDug4 : forall a b c d e s, done (MPrim "DUG" [MInt "4"] []) (a::b::c::d::e::s) (Some (b::c::d::e::a::s))
| DContract : forall s, done (MPrim "CONTRACT" [fa12_transfer_type] ["%transfer"]) (bare "address"::s) (Some (unary_type "option" (unary_type "contract" fa12_transfer_type)::s))
| DContractFA2 : forall s, done (MPrim "CONTRACT" [fa2_transfer_type] ["%transfer"]) (bare "address"::s) (Some (unary_type "option" (unary_type "contract" fa2_transfer_type)::s))
| DContractTicket : forall s, done (MPrim "CONTRACT" [ticket_type] []) (bare "address"::s) (Some (unary_type "option" (unary_type "contract" ticket_type)::s))
| DContractPool : forall s, done (MPrim "CONTRACT" [ingress_argument] []) (bare "address"::s) (Some (unary_type "option" (unary_type "contract" ingress_argument)::s))
| DContractImport : forall s, done (MPrim "CONTRACT" [import_argument] ["%import_ticket"]) (bare "address"::s) (Some (unary_type "option" (unary_type "contract" import_argument)::s))
| DSapling : forall s, done (MPrim "SAPLING_VERIFY_UPDATE" [] []) (transaction8::sapling8::s) (Some (unary_type "option" (MPrim "pair" [bare "bytes";bare "int";sapling8] [])::s))
| DUnpackAddress : forall s, done (MPrim "UNPACK" [bare "address"] []) (bare "bytes"::s) (Some (unary_type "option" (bare "address")::s))
| DPackAddress : forall s, done (MPrim "PACK" [] []) (bare "address"::s) (Some (bare "bytes"::s))
| DSizeBytes : forall s, done (MPrim "SIZE" [] []) (bare "bytes"::s) (Some (bare "nat"::s))
| DSizeList : forall a s, done (MPrim "SIZE" [] []) (unary_type "list" a::s) (Some (bare "nat"::s))
| DSizeMap : forall k v s, done (MPrim "SIZE" [] []) (MPrim "map" [k;v] []::s) (Some (bare "nat"::s))
| DEmptyMap : forall s, done (MPrim "EMPTY_MAP" [bare "address";bare "nat"] []) s (Some (MPrim "map" [bare "address";bare "nat"] []::s))
| DGetMap : forall s, done (MPrim "GET" [] []) (bare "address"::MPrim "map" [bare "address";bare "nat"] []::s) (Some (unary_type "option" (bare "nat")::s))
| DUpdateMap : forall s, done (MPrim "UPDATE" [] []) (bare "address"::unary_type "option" (bare "nat")::MPrim "map" [bare "address";bare "nat"] []::s) (Some (MPrim "map" [bare "address";bare "nat"] []::s))
| DSome : forall a s, done (MPrim "SOME" [] []) (a::s) (Some (unary_type "option" a::s))
| DAddNat : forall s, done (MPrim "ADD" [] []) (bare "nat"::bare "nat"::s) (Some (bare "nat"::s))
| DSubNat : forall s, done (MPrim "SUB" [] []) (bare "nat"::bare "nat"::s) (Some (bare "int"::s))
| DIntNat : forall s, done (MPrim "INT" [] []) (bare "nat"::s) (Some (bare "int"::s))
| DIsNat : forall s, done (MPrim "ISNAT" [] []) (bare "int"::s) (Some (unary_type "option" (bare "nat")::s))
| DNoneTicket : forall s, done (MPrim "NONE" [ticket_type] []) s (Some (unary_type "option" ticket_type::s))
| DReadTicket : forall s, done (MPrim "READ_TICKET" [] []) (ticket_type::s) (Some (pair_type (bare "address") (pair_type ticket_contents (bare "nat"))::ticket_type::s))
| DSplitTicket : forall s, done (MPrim "SPLIT_TICKET" [] []) (ticket_type::pair_type (bare "nat") (bare "nat")::s) (Some (unary_type "option" (pair_type ticket_type ticket_type)::s))
| DJoinTickets : forall s, done (MPrim "JOIN_TICKETS" [] []) (pair_type ticket_type ticket_type::s) (Some (unary_type "option" ticket_type::s))
| DSelf : forall s, done (MPrim "SELF_ADDRESS" [] []) s (Some (bare "address"::s))
| DSender : forall s, done (MPrim "SENDER" [] []) s (Some (bare "address"::s))
| DTransfer : forall s, done (MPrim "TRANSFER_TOKENS" [] []) (fa12_transfer_type::bare "mutez"::unary_type "contract" fa12_transfer_type::s) (Some (bare "operation"::s))
| DTransferFA2 : forall s, done (MPrim "TRANSFER_TOKENS" [] []) (fa2_transfer_type::bare "mutez"::unary_type "contract" fa2_transfer_type::s) (Some (bare "operation"::s))
| DTransferTicket : forall s, done (MPrim "TRANSFER_TOKENS" [] []) (ticket_type::bare "mutez"::unary_type "contract" ticket_type::s) (Some (bare "operation"::s))
| DTransferPool : forall s, done (MPrim "TRANSFER_TOKENS" [] []) (ingress_argument::bare "mutez"::unary_type "contract" ingress_argument::s) (Some (bare "operation"::s))
| DTransferImport : forall s, done (MPrim "TRANSFER_TOKENS" [] []) (import_argument::bare "mutez"::unary_type "contract" import_argument::s) (Some (bare "operation"::s))
| DCons : forall a s, done (MPrim "CONS" [] []) (a::unary_type "list" a::s) (Some (unary_type "list" a::s))
| DDip1 : forall a s body out, dseq body s (Some out) -> done (MPrim "DIP" [MSeq body] []) (a::s) (Some (a::out))
| DDip2 : forall a b s body out, dseq body s (Some out) -> done (MPrim "DIP" [MInt "2";MSeq body] []) (a::b::s) (Some (a::b::out))
| DDip3 : forall a b c s body out, dseq body s (Some out) -> done (MPrim "DIP" [MInt "3";MSeq body] []) (a::b::c::s) (Some (a::b::c::out))
| DIfBoth : forall y n s out, dseq y s (Some out) -> dseq n s (Some out) -> done (MPrim "IF" [MSeq y;MSeq n] []) (bare "bool"::s) (Some out)
| DIfYes : forall y n s out, dseq y s (Some out) -> dseq n s None -> done (MPrim "IF" [MSeq y;MSeq n] []) (bare "bool"::s) (Some out)
| DIfNo : forall y n s out, dseq y s None -> dseq n s (Some out) -> done (MPrim "IF" [MSeq y;MSeq n] []) (bare "bool"::s) (Some out)
| DIfNoneBoth : forall no yes a s out, dseq no s (Some out) -> dseq yes (a::s) (Some out) -> done (MPrim "IF_NONE" [MSeq no;MSeq yes] []) (unary_type "option" a::s) (Some out)
| DIfNoneYes : forall no yes a s out, dseq no s None -> dseq yes (a::s) (Some out) -> done (MPrim "IF_NONE" [MSeq no;MSeq yes] []) (unary_type "option" a::s) (Some out)
| DIfNoneNo : forall no yes a s out, dseq no s (Some out) -> dseq yes (a::s) None -> done (MPrim "IF_NONE" [MSeq no;MSeq yes] []) (unary_type "option" a::s) (Some out)
| DIterList : forall body a s, dseq body (a::s) (Some s) -> done (MPrim "ITER" [MSeq body] []) (unary_type "list" a::s) (Some s)
| DIterMap : forall body s, dseq body (pair_type (bare "address") (bare "nat")::s) (Some s) -> done (MPrim "ITER" [MSeq body] []) (MPrim "map" [bare "address";bare "nat"] []::s) (Some s)
| DMapList : forall body a b s, dseq body (a::s) (Some (b::s)) -> done (MPrim "MAP" [MSeq body] []) (unary_type "list" a::s) (Some (unary_type "list" b::s)).

Ltac dseq_proof :=
  lazymatch goal with
  | |- dseq [] _ _ => apply DEnd
  | |- dseq (?i :: ?tail) ?before ?out =>
      let result := eval vm_compute in (infer_seq 256 [i] before) in
      lazymatch result with
      | Some (Some ?middle) => eapply DNext with (mid := middle); [done_proof | dseq_proof]
      | Some None => apply DFail; done_proof
      | _ => fail 1 "unsupported typing hint" i
      end
  end
with done_proof :=
  first [ apply DNil | apply DNilFA2Entry | apply DNilFA2Group | apply DNilFA2Item | apply DNilTransaction | apply DNilTicket | apply DNilImport | apply DPair | apply DPair3 | apply DPair4 | apply DSwap | apply DAmount
    | apply DPushMutez | apply DPushNat0 | apply DPushNat28 | apply DPushFail | apply DPushString | apply DPushTrue
    | apply DCompareNat | apply DCompareMutez | apply DCompareAddress | apply DCompareTicketIdentity | apply DEq | apply DGt | apply DLt
    | apply DAbs | apply DUnit | apply DFailUnit | apply DFailString
    | (eapply DUnpair; reflexivity) | (eapply DUnpair3; reflexivity) | (eapply DUnpair4; reflexivity) | (eapply DCar; reflexivity) | (eapply DCdr; reflexivity)
    | apply DDupAddress | apply DDupInt | apply DDupContract | apply DDupFA2Contract | (eapply DDupAny; vm_compute; reflexivity)
    | lazymatch goal with |- done (MPrim "DUP" [MInt ?digit] []) _ _ =>
         let v := eval vm_compute in (small_nat (MInt digit)) in
         lazymatch v with Some (S ?n) => eapply (DDupN digit n); vm_compute; reflexivity end end
    | apply DDrop | apply DDrop2 | apply DDig2 | apply DDig3 | apply DDig4 | apply DDig5 | apply DDug2 | apply DDug3 | apply DDug4 | apply DContract | apply DContractFA2 | apply DContractTicket | apply DContractPool | apply DContractImport
    | apply DSapling | apply DUnpackAddress | apply DPackAddress | apply DSizeBytes | apply DSizeList | apply DSizeMap
    | apply DEmptyMap | apply DGetMap | apply DUpdateMap | apply DSome | apply DAddNat | apply DSubNat | apply DIntNat | apply DIsNat | apply DNoneTicket | apply DReadTicket | apply DSplitTicket | apply DJoinTickets
    | apply DSelf | apply DSender | apply DTransfer | apply DTransferFA2 | apply DTransferTicket | apply DTransferPool | apply DTransferImport | apply DCons
    | eapply DDip1; dseq_proof | eapply DDip2; dseq_proof | eapply DDip3; dseq_proof
    | eapply DIfBoth; [dseq_proof | dseq_proof]
    | eapply DIfYes; [dseq_proof | dseq_proof]
    | eapply DIfNo; [dseq_proof | dseq_proof]
    | eapply DIfNoneBoth; [dseq_proof | dseq_proof]
    | eapply DIfNoneYes; [dseq_proof | dseq_proof]
    | eapply DIfNoneNo; [dseq_proof | dseq_proof]
    | eapply DIterList; dseq_proof | eapply DIterMap; dseq_proof | eapply DMapList; dseq_proof ].

Theorem fa12_full_source_has_connected_declarative_typing :
 dseq fa12_code [fa12_input]
  (Some [pair_type list_operation (pair_type fa12_state (bare "address"))]).
Proof. cbn [fa12_code fa12_expected]. dseq_proof. Qed.
Print Assumptions fa12_full_source_has_connected_declarative_typing.

Theorem declared_fa12_source_has_connected_declarative_typing :
  forall before after,
    declared_input_output fa12_expected = Some (before,after) ->
    dseq fa12_code before (Some after).
Proof.
  intros before after H. rewrite fa12_declared_type_link in H. inversion H; subst.
  apply fa12_full_source_has_connected_declarative_typing.
Qed.
Print Assumptions declared_fa12_source_has_connected_declarative_typing.

Theorem fa2_full_source_has_connected_declarative_typing :
 dseq fa2_code [fa2_input]
  (Some [MPrim "pair" [list_operation;fa12_state;bare "address";bare "nat"] []]).
Proof. cbn [fa2_code fa2_expected]. dseq_proof. Qed.
Print Assumptions fa2_full_source_has_connected_declarative_typing.

Theorem declared_fa2_source_has_connected_declarative_typing :
  forall before after,
    declared_input_output fa2_expected = Some (before,after) ->
    dseq fa2_code before (Some after).
Proof.
  intros before after H. rewrite fa2_declared_type_link in H. inversion H; subst.
  apply fa2_full_source_has_connected_declarative_typing.
Qed.
Print Assumptions declared_fa2_source_has_connected_declarative_typing.

Theorem ticket_full_source_has_connected_declarative_typing :
 dseq ticket_code [pair_type ticket_parameter ticket_storage]
  (Some [pair_type list_operation ticket_storage]).
Proof. cbn [ticket_code ticket_expected]. dseq_proof. Qed.
Print Assumptions ticket_full_source_has_connected_declarative_typing.

Theorem declared_ticket_source_has_connected_declarative_typing :
  forall before after,
    declared_input_output ticket_expected = Some (before,after) ->
    dseq ticket_code before (Some after).
Proof.
  intros before after H. rewrite ticket_declared_type_link in H. inversion H; subst.
  apply ticket_full_source_has_connected_declarative_typing.
Qed.
Print Assumptions declared_ticket_source_has_connected_declarative_typing.

Theorem ingress_full_source_has_connected_declarative_typing :
 dseq ingress_code [pair_type ticket_type ingress_storage]
  (Some [pair_type list_operation ingress_storage]).
Proof. cbn [ingress_code ingress_expected]. dseq_proof. Qed.
Print Assumptions ingress_full_source_has_connected_declarative_typing.

Theorem egress_full_source_has_connected_declarative_typing :
 dseq egress_code [pair_type ticket_type egress_storage]
  (Some [pair_type list_operation egress_storage]).
Proof. cbn [egress_code egress_expected]. dseq_proof. Qed.
Print Assumptions egress_full_source_has_connected_declarative_typing.

Theorem declared_ingress_source_has_connected_declarative_typing :
  forall before after,
    declared_input_output ingress_expected = Some (before,after) ->
    dseq ingress_code before (Some after).
Proof.
  intros before after H. rewrite ingress_declared_type_link in H. inversion H; subst.
  apply ingress_full_source_has_connected_declarative_typing.
Qed.
Theorem declared_egress_source_has_connected_declarative_typing :
  forall before after,
    declared_input_output egress_expected = Some (before,after) ->
    dseq egress_code before (Some after).
Proof.
  intros before after H. rewrite egress_declared_type_link in H. inversion H; subst.
  apply egress_full_source_has_connected_declarative_typing.
Qed.
Print Assumptions declared_ingress_source_has_connected_declarative_typing.
Print Assumptions declared_egress_source_has_connected_declarative_typing.
