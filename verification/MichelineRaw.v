(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String Arith.
Import ListNotations.
Open Scope string_scope.

(* The scalar payloads are exact strings from canonical Micheline JSON.
   Integer and bytes lexical validity, UTF-8, source locations, protocol
   primitive vocabulary and JSON parsing are separate obligations. *)
Inductive node : Type :=
| MInt (decimal : string) | MString (text : string) | MBytes (hex : string)
| MPrim (name : string) (args : list node) (annotations : list string)
| MSeq (items : list node).

(* This decidable equality compares the complete raw tree, including all
   arguments and annotations; it is independent of Michelson typing. *)
Fixpoint node_eq_dec (x y : node) : {x = y} + {x <> y}.
Proof.
  decide equality; try apply string_dec;
    try (apply list_eq_dec; apply string_dec);
    apply list_eq_dec; exact node_eq_dec.
Defined.

(* Prefix frames carry explicit arities. Unlike the existing translation,
   neither types nor annotations nor a COMPARE interpretation are erased. *)
Inductive token : Type :=
| TInt (decimal : string) | TString (text : string) | TBytes (hex : string)
| TPrim (name : string) (arity : nat) (annotations : list string)
| TSeq (arity : nat).

Fixpoint decode (fuel : nat) (input : list token) : option (node * list token) :=
  match fuel, input with
  | O, _ | _, [] => None
  | S f, t :: rest =>
      let fix children n xs :=
        match n with
        | O => Some ([], xs)
        | S n' =>
            match decode f xs with
            | None => None
            | Some (v, tail) =>
                match children n' tail with
                | None => None
                | Some (vs, final) => Some (v :: vs, final)
                end
            end
        end in
      match t with
      | TInt x => Some (MInt x, rest)
      | TString x => Some (MString x, rest)
      | TBytes x => Some (MBytes x, rest)
      | TPrim name n annots =>
          match children n rest with
          | Some (args, tail) => Some (MPrim name args annots, tail)
          | None => None end
      | TSeq n =>
          match children n rest with
          | Some (items, tail) => Some (MSeq items, tail)
          | None => None end
      end
  end.

Definition decode_complete fuel input : option node :=
  match decode fuel input with
  | Some (v, []) => Some v
  | _ => None
  end.

Example no_context_dependent_compare :
  decode_complete 3 [TSeq 2; TPrim "COMPARE" 0 []; TPrim "COMPARE" 0 []] =
  Some (MSeq [MPrim "COMPARE" [] []; MPrim "COMPARE" [] []]).
Proof. reflexivity. Qed.

Example retains_typed_arguments_and_annotations :
  decode_complete 4 [TPrim "PUSH" 2 ["@result"]; TPrim "nat" 0 []; TInt "28"] =
  Some (MPrim "PUSH" [MPrim "nat" [] []; MInt "28"] ["@result"]).
Proof. reflexivity. Qed.

Example rejects_truncated_and_trailing_inputs :
  decode_complete 3 [TPrim "DIP" 1 []] = None /\
  decode_complete 3 [TPrim "DROP" 0 []; TPrim "DROP" 0 []] = None.
Proof. split; reflexivity. Qed.
