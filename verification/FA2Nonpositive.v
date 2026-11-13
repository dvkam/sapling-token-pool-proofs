From Coq Require Import List ZArith String.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* A source-extractable prefix shared by the nonpositive branches of the FA2
   Sapling loop. READ/crypto/token semantics are outside this lemma. *)
Definition bound_data_check : list instruction :=
  [Dig 3; Size; Push (VNat 0); CompareInt; IsEq; If [] [Unit; Fail]].

Section Nonpositive.
  Variable primitive : string -> stack -> option stack.

  Theorem empty_bound_data_passes : forall first second third rest,
    run primitive 20 bound_data_check
      (first :: second :: third :: VBytes [] :: rest) =
    Some (first :: second :: third :: rest).
  Proof. intros; reflexivity. Qed.

  Theorem nonempty_bound_data_fails : forall first second third byte bytes rest,
    run primitive 20 bound_data_check
      (first :: second :: third :: VBytes (byte :: bytes) :: rest) = None.
  Proof. intros; reflexivity. Qed.
End Nonpositive.
