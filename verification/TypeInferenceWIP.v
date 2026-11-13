(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String Arith Bool.
Require Import MichelineRaw MichelinePrograms.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* WORK IN PROGRESS. Unsupported rules return None. Some None means the
   instruction always fails; Some (Some s) means a continuing typed stack.
   This is a type-level experiment, not Octez execution or a whole-program
   proof. The soundness of this function against native typing rules is still open. *)
Definition typed_stack := list node.
Definition outcome := option typed_stack.
Definition bare s := MPrim s [] [].
Definition unary_type name arg := MPrim name [arg] [].
Definition pair_type a b := match b with
  | MPrim "pair" (x :: y :: rest) [] => MPrim "pair" (a :: x :: y :: rest) []
  | _ => MPrim "pair" [a;b] [] end.
Definition list_operation := unary_type "list" (bare "operation").
Definition ticket_identity_type := MPrim "pair" [bare "address";bare "nat"; unary_type "option" (bare "bytes")] [].
Definition supported_compare_type (t : node) : bool :=
  if node_eq_dec t (bare "nat") then true else
  if node_eq_dec t (bare "mutez") then true else
  if node_eq_dec t (bare "address") then true else
  if node_eq_dec t ticket_identity_type then true else false.
Definition fa12_code : list node :=
  match fa12_expected with MSeq [_;_;MPrim "code" [MSeq code] _] => code | _ => [] end.
Definition fa12_state := MPrim "sapling_state" [MInt "8"] [].
Definition fa12_parameter := unary_type "list" (MPrim "sapling_transaction" [MInt "8"] []).
Definition fa12_input := MPrim "pair" [fa12_parameter;fa12_state;bare "address"] [].
Definition fa12_transfer_type := MPrim "pair" [bare "address";bare "address";bare "nat"] [].
Definition fa12_frame := [unary_type "contract" fa12_transfer_type;bare "address";pair_type list_operation list_operation].
Definition fa12_iteration_body : list node :=
  match nth_error fa12_code 11 with Some (MPrim "ITER" [MSeq body] _) => body | _ => [] end.
Definition combine (left right : outcome) : option outcome :=
  match left,right with
  | None,None => Some None
  | Some s,None | None,Some s => Some (Some s)
  | Some a,Some b => if list_eq_dec node_eq_dec a b then Some (Some a) else None
  end.
Definition two_args3 := MPrim "pair" [bare "address";bare "address";bare "nat"] [].
Definition sapling8 := MPrim "sapling_state" [MInt "8"] [].
Definition transaction8 := MPrim "sapling_transaction" [MInt "8"] [].
Fixpoint comparable_type (fuel : nat) (t : node) : bool :=
  match fuel,t with
  | O,_ => false
  | S f,MPrim p args [] =>
      if existsb (String.eqb p) ["unit";"int";"nat";"string";"bytes";"mutez";"address";"bool"]
      then match args with [] => true | _ => false end
      else if String.eqb p "option" then
        match args with [a] => comparable_type f a | _ => false end
      else if String.eqb p "pair" then
        match args with _ :: _ :: _ => forallb (comparable_type f) args | _ => false end
      else false
  | _,_ => false end.
Fixpoint valid_type (fuel : nat) (t : node) : bool :=
  match fuel,t with
  | O,_ => false
  | S f,MPrim p args [] =>
      if comparable_type (S f) t then true else
      if existsb (String.eqb p) ["operation"] then
        match args with [] => true | _ => false end
      else if existsb (String.eqb p) ["sapling_state";"sapling_transaction"] then
        match args with [MInt "8"] => true | _ => false end
      else if existsb (String.eqb p) ["list";"option";"contract"] then
        match args with [a] => valid_type f a | _ => false end
      else if String.eqb p "ticket" then
        match args with [a] => comparable_type f a | _ => false end
      else if String.eqb p "pair" then
        match args with _ :: _ :: _ => forallb (valid_type f) args | _ => false end
      else if String.eqb p "map" then
        match args with [k;v] => comparable_type f k && valid_type f v | _ => false end
      else false
  | _,_ => false end.
(* Conservative accepted annotations for these five scripts. This is not a
   general Michelson annotation parser. *)
Definition annotations_allowed (instruction : node) : bool :=
  match instruction with
  | MPrim "CONTRACT" _ [] => true
  | MPrim "CONTRACT" _ ["%transfer"] => true
  | MPrim "CONTRACT" _ ["%import_ticket"] => true
  | MPrim _ _ [] => true
  | _ => false end.
Fixpoint pair_args (xs : list node) : option node :=
  match xs with
  | [] => None | [x] => Some x
  | x :: rest => match pair_args rest with Some y => Some (pair_type x y) | None => None end
  end.
Fixpoint normalize_declared_type (fuel : nat) (t : node) : option node :=
  match fuel with
  | O => None
  | S f => match t with
    | MInt n => Some (MInt n)
    | MPrim p args _ =>
      let fix norm_args xs := match xs with
        | [] => Some []
        | x :: rest => match normalize_declared_type f x, norm_args rest with
          | Some a,Some b => Some (a :: b) | _,_ => None end end in
      match norm_args args with
      | None => None
      | Some normalized => if String.eqb p "pair" then
          match normalized with _ :: _ :: _ => pair_args normalized | _ => None end
          else Some (MPrim p normalized [])
      end
    | _ => None end
  end.
Fixpoint find_field (name : string) (xs : list node) : option node :=
  match xs with
  | [] => None
  | MPrim p [v] _ :: rest => if String.eqb p name then Some v else find_field name rest
  | _ :: rest => find_field name rest end.
Definition declared_input_output (program : node) : option (typed_stack * typed_stack) :=
  match program with
  | MSeq fields => match find_field "parameter" fields, find_field "storage" fields with
    | Some p, Some s => match normalize_declared_type 64 p, normalize_declared_type 64 s with
      | Some p',Some s' => Some ([pair_type p' s'], [pair_type list_operation s'])
      | _,_ => None end
    | _,_ => None end
  | _ => None end.
Definition small_nat (x : node) : option nat :=
  match x with
  | MInt "0" => Some 0 | MInt "1" => Some 1 | MInt "2" => Some 2
  | MInt "3" => Some 3 | MInt "4" => Some 4 | MInt "5" => Some 5
  | MInt "6" => Some 6 | MInt "7" => Some 7 | MInt "8" => Some 8
  | _ => None end.
Definition index_arg (args : list node) (default : nat) : option nat :=
  match args with [] => Some default | [x] => small_nat x | _ => None end.
Definition unpair_type (t : node) : option (node * node) :=
  match t with
  | MPrim "pair" (a :: b :: rest) [] =>
      Some (a, match rest with [] => b | _ => MPrim "pair" (b :: rest) [] end)
  | _ => None end.
Fixpoint pair_types (n : nat) (s : typed_stack) : option typed_stack :=
  match n, s with
  | 2, a :: b :: rest => Some (pair_type a b :: rest)
  | S (S (S k)), a :: rest =>
      match pair_types (S (S k)) rest with
      | Some (b :: tail) => Some (pair_type a b :: tail) | _ => None end
  | _, _ => None end.
Fixpoint unpair_types (n : nat) (t : node) : option (list node) :=
  match n with
  | O => None | 1 => Some [t]
  | S n' => match unpair_type t with
      | Some (a,b) => match unpair_types n' b with Some rest => Some (a :: rest) | None => None end
      | None => None end
  end.
Fixpoint dupable (fuel : nat) (t : node) : bool :=
  match fuel with
  | O => false
  | S f => match t with
    | MPrim p args _ =>
      if String.eqb p "ticket" then false else
      if existsb (String.eqb p) ["pair";"or";"option";"list";"map";"big_map"]
      then forallb (dupable f) args
      else existsb (String.eqb p) ["unit";"int";"nat";"string";"bytes";"mutez";"address";"bool";"contract";"operation";"sapling_state";"sapling_transaction"]
    | _ => false end
  end.

Fixpoint infer_seq (fuel : nat) (code : list node) (stack : typed_stack) : option outcome :=
  match fuel with
  | O => None
  | S f => if forallb (valid_type 64) stack then
    match code with
    | [] => Some (Some stack)
    | instruction :: tail =>
      let step := if annotations_allowed instruction then
        match instruction with
        | MPrim "NIL" [t] _ => if valid_type 64 t then Some (Some (unary_type "list" t :: stack)) else None
        | MPrim "UNIT" [] _ => Some (Some (bare "unit" :: stack))
        | MPrim "AMOUNT" [] _ => Some (Some (bare "mutez" :: stack))
        | MPrim "PUSH" [MPrim "mutez" [] []; MInt "0"] _ => Some (Some (bare "mutez" :: stack))
        | MPrim "PUSH" [MPrim "nat" [] []; MInt "0"] _ => Some (Some (bare "nat" :: stack))
        | MPrim "PUSH" [MPrim "nat" [] []; MInt "28"] _ => Some (Some (bare "nat" :: stack))
        | MPrim "PUSH" [MPrim "string" [] []; MString _] _ => Some (Some (bare "string" :: stack))
        | MPrim "PUSH" [MPrim "bool" [] []; MPrim "True" [] []] _ => Some (Some (bare "bool" :: stack))
        | MPrim "FAILWITH" [] [] => match stack with
            | MPrim "unit" [] [] :: _ | MPrim "string" [] [] :: _ => Some None
            | _ => None end
        | MPrim "PAIR" args _ => match index_arg args 2 with
          | Some n => match pair_types n stack with Some out => Some (Some out) | None => None end
          | None => None end
        | MPrim "SWAP" [] _ => match stack with a :: b :: rest => Some (Some (b :: a :: rest)) | _ => None end
        | MPrim "SOME" [] _ => match stack with a :: rest => Some (Some (unary_type "option" a :: rest)) | _ => None end
        | MPrim "NONE" [a] _ => if valid_type 64 a then Some (Some (unary_type "option" a :: stack)) else None
        | MPrim "EMPTY_MAP" [k;v] _ => if comparable_type 64 k && valid_type 64 v then Some (Some (MPrim "map" [k;v] [] :: stack)) else None
        | MPrim "GET" [] _ => match stack with k :: MPrim "map" [kt;v] [] :: rest =>
             if node_eq_dec k kt then Some (Some (unary_type "option" v :: rest)) else None | _ => None end
        | MPrim "UPDATE" [] _ => match stack with k :: MPrim "option" [v] [] :: MPrim "map" [kt;vt] [] :: rest =>
             if node_eq_dec k kt then if node_eq_dec v vt then Some (Some (MPrim "map" [kt;vt] [] :: rest)) else None else None | _ => None end
        | MPrim "CAR" [] _ => match stack with a :: rest => match unpair_type a with
           | Some (left_type,_) => Some (Some (left_type :: rest)) | _ => None end | _ => None end
        | MPrim "CDR" [] _ => match stack with a :: rest => match unpair_type a with
           | Some (_,right_type) => Some (Some (right_type :: rest)) | _ => None end | _ => None end
        | MPrim "CONS" [] _ => match stack with
           | a :: MPrim "list" [t] [] :: rest => if node_eq_dec a t
              then Some (Some (unary_type "list" t :: rest)) else None | _ => None end
        | MPrim "DUP" args _ => match index_arg args 1 with
           | Some (S n) => match nth_error stack n with
             | Some t => if dupable 32 t then Some (Some (t :: stack)) else None | None => None end
           | _ => None end
        | MPrim "DROP" args _ => match index_arg args 1 with
           | Some n => if Nat.leb n (List.length stack) then Some (Some (skipn n stack)) else None
           | None => None end
        | MPrim "DIG" args _ => match (match args with [x] => small_nat x | _ => None end) with
           | Some n => match nth_error stack n with
             | Some t => Some (Some (t :: firstn n stack ++ skipn (S n) stack)) | None => None end
           | None => None end
        | MPrim "DUG" args _ => match (match args with [x] => small_nat x | _ => None end), stack with
           | Some n, t :: rest => if Nat.leb n (List.length rest)
             then Some (Some (firstn n rest ++ t :: skipn n rest)) else None
           | _,_ => None end
        | MPrim "COMPARE" [] _ => match stack with a :: b :: rest =>
           if node_eq_dec a b then if supported_compare_type a then Some (Some (bare "int" :: rest)) else None else None
           | _ => None end
        | MPrim "EQ" [] _ => match stack with MPrim "int" [] [] :: rest => Some (Some (bare "bool" :: rest)) | _ => None end
        | MPrim "GT" [] _ => match stack with MPrim "int" [] [] :: rest => Some (Some (bare "bool" :: rest)) | _ => None end
        | MPrim "LT" [] _ => match stack with MPrim "int" [] [] :: rest => Some (Some (bare "bool" :: rest)) | _ => None end
        | MPrim "ABS" [] _ => match stack with MPrim "int" [] [] :: rest => Some (Some (bare "nat" :: rest)) | _ => None end
        | MPrim "ADD" [] _ => match stack with MPrim "nat" [] [] :: MPrim "nat" [] [] :: rest => Some (Some (bare "nat" :: rest)) | _ => None end
        | MPrim "SUB" [] _ => match stack with MPrim "nat" [] [] :: MPrim "nat" [] [] :: rest => Some (Some (bare "int" :: rest)) | _ => None end
        | MPrim "INT" [] _ => match stack with MPrim "nat" [] [] :: rest => Some (Some (bare "int" :: rest)) | _ => None end
        | MPrim "ISNAT" [] _ => match stack with MPrim "int" [] [] :: rest => Some (Some (unary_type "option" (bare "nat") :: rest)) | _ => None end
        | MPrim "READ_TICKET" [] _ => match stack with
           | MPrim "ticket" [t] [] :: rest => Some (Some (pair_type (bare "address") (pair_type t (bare "nat")) :: unary_type "ticket" t :: rest)) | _ => None end
        | MPrim "SPLIT_TICKET" [] _ => match stack with
           | MPrim "ticket" [t] [] :: amounts :: rest =>
             if node_eq_dec amounts (pair_type (bare "nat") (bare "nat"))
             then Some (Some (unary_type "option" (pair_type (unary_type "ticket" t) (unary_type "ticket" t)) :: rest)) else None | _ => None end
        | MPrim "JOIN_TICKETS" [] _ => match stack with
           | pairs :: rest => match unpair_type pairs with
             | Some (MPrim "ticket" [a] [], MPrim "ticket" [b] []) =>
                 if node_eq_dec a b then Some (Some (unary_type "option" (unary_type "ticket" a) :: rest)) else None
             | _ => None end | _ => None end
        | MPrim "SELF_ADDRESS" [] _ | MPrim "SENDER" [] _ => Some (Some (bare "address" :: stack))
        | MPrim "PACK" [] _ => match stack with MPrim "address" [] [] :: rest => Some (Some (bare "bytes" :: rest)) | _ => None end
        | MPrim "UNPACK" [MPrim "address" [] []] _ => match stack with
            | MPrim "bytes" [] [] :: rest => Some (Some (unary_type "option" (bare "address") :: rest)) | _ => None end
        | MPrim "SIZE" [] _ => match stack with
            | MPrim "bytes" [] [] :: rest => Some (Some (bare "nat" :: rest))
            | MPrim "string" [] [] :: rest => Some (Some (bare "nat" :: rest))
            | MPrim "list" [_] [] :: rest => Some (Some (bare "nat" :: rest))
            | MPrim "map" [_;_] [] :: rest => Some (Some (bare "nat" :: rest)) | _ => None end
        | MPrim "UNPAIR" args _ => match index_arg args 2, stack with
           | Some n, t :: rest => if Nat.leb 2 n then match unpair_types n t with Some ts => Some (Some (ts ++ rest)) | None => None end else None
           | _, _ => None end
        | MPrim "CONTRACT" [arg] _ => match stack with
           | MPrim "address" [] [] :: rest => if valid_type 64 arg then Some (Some (unary_type "option" (unary_type "contract" arg) :: rest)) else None
           | _ => None end
        | MPrim "TRANSFER_TOKENS" [] _ => match stack with
           | arg :: MPrim "mutez" [] [] :: MPrim "contract" [t] [] :: rest =>
             if node_eq_dec arg t then Some (Some (bare "operation" :: rest)) else None | _ => None end
        | MPrim "SAPLING_VERIFY_UPDATE" [] _ => match stack with
           | a :: b :: rest => if node_eq_dec a transaction8 then if node_eq_dec b sapling8
             then Some (Some (unary_type "option" (MPrim "pair" [bare "bytes";bare "int";sapling8] []) :: rest)) else None else None
           | _ => None end
        | MPrim "DIP" args _ =>
          let parsed := match args with [MSeq body] => Some (1,body)
             | [n;MSeq body] => match small_nat n with Some d => Some (d,body) | None => None end
             | _ => None end in
          match parsed with
          | Some (n,body) => if Nat.leb n (List.length stack) then
             match infer_seq f body (skipn n stack) with
             | Some (Some output) => Some (Some (firstn n stack ++ output)) | _ => None end else None
          | None => None end
        | MPrim "ITER" [MSeq body] _ => match stack with
           | MPrim "list" [a] [] :: rest => match infer_seq f body (a :: rest) with
              | Some (Some output) => if list_eq_dec node_eq_dec output rest then Some (Some rest) else None
              | _ => None end
           | MPrim "map" [k;v] [] :: rest => match infer_seq f body (pair_type k v :: rest) with
              | Some (Some output) => if list_eq_dec node_eq_dec output rest then Some (Some rest) else None
              | _ => None end
           | _ => None end
        | MPrim "MAP" [MSeq body] _ => match stack with
           | MPrim "list" [a] [] :: rest => match infer_seq f body (a :: rest) with
              | Some (Some (b :: output)) => if list_eq_dec node_eq_dec output rest
                 then Some (Some (unary_type "list" b :: rest)) else None | _ => None end
           | _ => None end
        | MPrim "IF" [MSeq yes; MSeq no] _ => match stack with
           | MPrim "bool" [] [] :: rest => match infer_seq f yes rest, infer_seq f no rest with
             | Some yes_result,Some no_result => combine yes_result no_result | _,_ => None end
           | _ => None end
        | MPrim "IF_NONE" [MSeq none; MSeq some] _ => match stack with
           | MPrim "option" [value] [] :: rest => match infer_seq f none rest, infer_seq f some (value :: rest) with
             | Some none_result,Some some_result => combine none_result some_result | _,_ => None end
           | _ => None end
        | _ => None
        end else None in
      match step with
      | None => None
      | Some None => match tail with [] => Some None | _ => None end
      | Some (Some next) => infer_seq f tail next
      end
    end else None
  end.

Example reflective_fa12_initialization :
 infer_seq 128 (firstn 11 fa12_code) [fa12_input] =
 Some (Some [fa12_parameter;fa12_state;unary_type "contract" fa12_transfer_type;
             bare "address";pair_type list_operation list_operation]).
Proof. vm_compute. reflexivity. Qed.
Example reflective_fa12_iteration_prefix :
 infer_seq 128 (firstn 9 fa12_iteration_body)
  (transaction8 :: fa12_state :: fa12_frame) =
 Some (Some (bare "bool" :: bare "int" :: bare "nat" :: fa12_state :: bare "bytes" :: fa12_frame)).
Proof. vm_compute. reflexivity. Qed.

(* This computes a connected type transition on the whole decoded FA1.2
   script. The checker-to-declarative proof and protocol correspondence are
   still open, so this computation alone is not a Michelson typing theorem. *)
Example fa12_full_program_reflective_result :
 infer_seq 256 fa12_code [fa12_input] =
 Some (Some [pair_type list_operation (pair_type fa12_state (bare "address"))]).
Proof. vm_compute. reflexivity. Qed.

Definition fa2_code : list node :=
  match fa2_expected with MSeq [_;_;MPrim "code" [MSeq code] _] => code | _ => [] end.
Definition fa2_input := MPrim "pair" [fa12_parameter; fa12_state; bare "address"; bare "nat"] [].
Example fa2_full_program_reflective_result :
 infer_seq 256 fa2_code [fa2_input] =
 Some (Some [MPrim "pair" [list_operation;fa12_state;bare "address";bare "nat"] []]).
Proof. vm_compute. reflexivity. Qed.

Definition ticket_contents := pair_type (bare "nat") (unary_type "option" (bare "bytes")).
Definition ticket_type := unary_type "ticket" ticket_contents.
Definition ticket_parameter := pair_type (unary_type "option" ticket_type) fa12_parameter.
Definition ticket_storage := MPrim "pair" [fa12_state;unary_type "option" ticket_type;bare "address";bare "nat";unary_type "option" (bare "bytes")] [].
Definition ticket_code : list node :=
  match ticket_expected with MSeq [_;_;MPrim "code" [MSeq code] _] => code | _ => [] end.
Example ticket_full_program_reflective_result :
 infer_seq 256 ticket_code [pair_type ticket_parameter ticket_storage] =
 Some (Some [pair_type list_operation ticket_storage]).
Proof. vm_compute. reflexivity. Qed.

Definition adapter_identity := pair_type (bare "address") ticket_contents.
Definition ingress_storage := MPrim "pair" [bare "address";adapter_identity;transaction8;bare "bool"] [].
Definition egress_storage := MPrim "pair" [bare "address";adapter_identity;bare "address"] [].
Definition ingress_code : list node :=
  match ingress_expected with MSeq [_;_;MPrim "code" [MSeq code] _] => code | _ => [] end.
Definition egress_code : list node :=
  match egress_expected with MSeq [_;_;MPrim "code" [MSeq code] _] => code | _ => [] end.
Example ingress_full_program_reflective_result :
 infer_seq 256 ingress_code [pair_type ticket_type ingress_storage] =
 Some (Some [pair_type list_operation ingress_storage]).
Proof. vm_compute. reflexivity. Qed.
Example egress_full_program_reflective_result :
 infer_seq 256 egress_code [pair_type ticket_type egress_storage] =
 Some (Some [pair_type list_operation egress_storage]).
Proof. vm_compute. reflexivity. Qed.

Example fa12_declared_type_link : declared_input_output fa12_expected =
 Some ([fa12_input], [pair_type list_operation (pair_type fa12_state (bare "address"))]).
Proof. vm_compute. reflexivity. Qed.
Example fa2_declared_type_link : declared_input_output fa2_expected =
 Some ([fa2_input], [MPrim "pair" [list_operation;fa12_state;bare "address";bare "nat"] []]).
Proof. vm_compute. reflexivity. Qed.
Example ticket_declared_type_link : declared_input_output ticket_expected =
 Some ([pair_type ticket_parameter ticket_storage], [pair_type list_operation ticket_storage]).
Proof. vm_compute. reflexivity. Qed.
Example ingress_declared_type_link : declared_input_output ingress_expected =
 Some ([pair_type ticket_type ingress_storage], [pair_type list_operation ingress_storage]).
Proof. vm_compute. reflexivity. Qed.
Example egress_declared_type_link : declared_input_output egress_expected =
 Some ([pair_type ticket_type egress_storage], [pair_type list_operation egress_storage]).
Proof. vm_compute. reflexivity. Qed.
