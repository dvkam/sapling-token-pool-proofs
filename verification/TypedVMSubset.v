(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith Arith Bool String.
Require Import FullVM_WIP MichelineRaw MichelinePrograms TypeInferenceWIP.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* A small intrinsically typed stack machine for a pure subset of the pinned
   Octez typed interpreter. Its transition equations follow I... cases in
   script_interpreter.ml:657-740,1023-1048,1160-1193. This is an independent
   Coq specification, not an extraction of OCaml or a proof about the native
   implementation. Types/values outside this subset, gas, errors and all
   context-dependent primitives remain outside this bridge. *)
Inductive mtype := MNat | MInt | MBool | MUnit | MPair (a b : mtype) | MList (a : mtype).
Fixpoint denotation (t : mtype) : Type :=
  match t with
  | MNat => nat | MInt => Z | MBool => bool | MUnit => unit
  | MPair a b => (denotation a * denotation b)%type
  | MList a => list (denotation a)
  end.
Fixpoint erase_value (t : mtype) : denotation t -> value :=
  match t as ty return denotation ty -> value with
  | MNat => VNat | MInt => VInt | MBool => VBool | MUnit => fun _ => VUnit
  | MPair a b => fun v => VPair (erase_value a (fst v)) (erase_value b (snd v))
  | MList a => fun xs => VList (map (erase_value a) xs)
  end.
Fixpoint typed_stack (ts : list mtype) : Type :=
  match ts with [] => unit | t :: rest => (denotation t * typed_stack rest)%type end.
Fixpoint erase_stack (ts : list mtype) : typed_stack ts -> stack :=
  match ts as types return typed_stack types -> stack with
  | [] => fun _ => []
  | t :: rest => fun s => erase_value t (fst s) :: erase_stack rest (snd s)
  end.

Inductive kinstr : list mtype -> list mtype -> Type :=
| KDrop : forall a s, kinstr (a :: s) s
| KDup : forall a s, kinstr (a :: s) (a :: a :: s)
| KSwap : forall a b s, kinstr (a :: b :: s) (b :: a :: s)
| KPair : forall a b s, kinstr (a :: b :: s) (MPair a b :: s)
| KUnpair : forall a b s, kinstr (MPair a b :: s) (a :: b :: s)
| KCar : forall a b s, kinstr (MPair a b :: s) (a :: s)
| KCdr : forall a b s, kinstr (MPair a b :: s) (b :: s)
| KNil : forall a s, kinstr s (MList a :: s)
| KCons : forall a s, kinstr (a :: MList a :: s) (MList a :: s)
| KUnit : forall s, kinstr s (MUnit :: s)
| KAbs : forall s, kinstr (MInt :: s) (MNat :: s)
| KAddNat : forall s, kinstr (MNat :: MNat :: s) (MNat :: s)
| KSubNat : forall s, kinstr (MNat :: MNat :: s) (MInt :: s)
| KCompareNat : forall s, kinstr (MNat :: MNat :: s) (MInt :: s)
| KEq : forall s, kinstr (MInt :: s) (MBool :: s).

Definition compare_nat_z a b : Z :=
  match Nat.compare a b with Lt => -1 | Eq => 0 | Gt => 1 end.
Definition execute {i o} (op : kinstr i o) : typed_stack i -> typed_stack o :=
  match op in kinstr input output return typed_stack input -> typed_stack output with
  | KDrop _ _ => fun s => snd s
  | KDup _ _ => fun s => (fst s, (fst s, snd s))
  | KSwap _ _ _ => fun s => (fst (snd s), (fst s, snd (snd s)))
  | KPair _ _ _ => fun s => ((fst s, fst (snd s)), snd (snd s))
  | KUnpair _ _ _ => fun s => (fst (fst s), (snd (fst s), snd s))
  | KCar _ _ _ => fun s => (fst (fst s), snd s)
  | KCdr _ _ _ => fun s => (snd (fst s), snd s)
  | KNil _ _ => fun s => ([], s)
  | KCons _ _ => fun s => (fst s :: fst (snd s), snd (snd s))
  | KUnit _ => fun s => (tt, s)
  | KAbs _ => fun s => (Z.to_nat (Z.abs (fst s)), snd s)
  | KAddNat _ => fun s => ((fst s + fst (snd s))%nat, snd (snd s))
  | KSubNat _ => fun s => (Z.of_nat (fst s) - Z.of_nat (fst (snd s)), snd (snd s))
  | KCompareNat _ => fun s => (compare_nat_z (fst s) (fst (snd s)), snd (snd s))
  | KEq _ => fun s => (Z.eqb (fst s) 0, snd s)
  end.
Definition erase_instruction {i o} (op : kinstr i o) : instruction :=
  match op with
  | KDrop _ _ => Drop | KDup _ _ => Dup 1 | KSwap _ _ _ => Swap
  | KPair _ _ _ => Pair | KUnpair _ _ _ => Unpair
  | KCar _ _ _ => Car | KCdr _ _ _ => Cdr | KNil _ _ => Nil
  | KCons _ _ => Cons | KUnit _ => Unit | KAbs _ => Abs
  | KAddNat _ => Add | KSubNat _ => Sub | KCompareNat _ => CompareInt | KEq _ => IsEq
  end.

Theorem typed_instruction_erasure_simulates_vm :
  forall prim i o (op : kinstr i o) (s : typed_stack i),
    run prim 3 [erase_instruction op] (erase_stack i s) =
      Some (erase_stack o (execute op s)).
Proof.
  intros prim i o op. destruct op; intros st;
    repeat match goal with x : (_ * _)%type |- _ => destruct x end;
    cbn [erase_instruction erase_stack execute erase_value run compare_nat_z]; reflexivity.
Qed.
Print Assumptions typed_instruction_erasure_simulates_vm.

Lemma typed_instruction_preserves_continuation :
  forall prim i o (op : kinstr i o) (s : typed_stack i) fuel tail,
    run prim (S fuel) (erase_instruction op :: tail) (erase_stack i s) =
      run prim fuel tail (erase_stack o (execute op s)).
Proof.
  intros prim i o op. destruct op; intros st fuel tail;
    repeat match goal with x : (_ * _)%type |- _ => destruct x end;
    cbn [erase_instruction erase_stack execute erase_value run compare_nat_z]; reflexivity.
Qed.

Inductive program : list mtype -> list mtype -> Type :=
| PHalt : forall s, program s s
| PNext : forall a b c, kinstr a b -> program b c -> program a c.
Fixpoint erase_program {i o} (p : program i o) : list instruction :=
  match p with PHalt _ => [] | PNext _ _ _ op rest => erase_instruction op :: erase_program rest end.
Fixpoint execute_program {i o} (p : program i o) : typed_stack i -> typed_stack o :=
  match p in program input output return typed_stack input -> typed_stack output with
  | PHalt _ => fun s => s
  | PNext _ _ _ op rest => fun s => execute_program rest (execute op s)
  end.
Theorem typed_program_erasure_simulates_vm :
  forall prim i o (p : program i o) (s : typed_stack i),
    run prim (S (List.length (erase_program p))) (erase_program p) (erase_stack i s) =
      Some (erase_stack o (execute_program p s)).
Proof.
  intros prim i o p. induction p as [s|a b c op rest IH]; intros stack.
  - reflexivity.
  - cbn [erase_program List.length]. rewrite typed_instruction_preserves_continuation.
    apply IH.
Qed.
Print Assumptions typed_program_erasure_simulates_vm.

(* Actual FA1.2 iteration-body fragment: the two DUPs and ABS operate on a
   signed public balance. This connects a raw decoded source fragment to a
   typed program and then uses the generic erasure simulation above. *)
Definition fa12_dup_abs_typed : program [MInt] [MNat;MInt;MInt].
Proof.
  eapply PNext. exact (KDup MInt []).
  eapply PNext. exact (KDup MInt [MInt]).
  eapply PNext. exact (KAbs [MInt;MInt]).
  apply PHalt.
Defined.
Example fa12_dup_abs_exact_raw_source :
  firstn 3 (skipn 4 fa12_iteration_body) =
  [MPrim "DUP" [] []; MPrim "DUP" [] []; MPrim "ABS" [] []].
Proof. vm_compute. reflexivity. Qed.
Example fa12_dup_abs_erases_to_vm : erase_program fa12_dup_abs_typed = [Dup 1; Dup 1; Abs].
Proof. reflexivity. Qed.
Theorem fa12_dup_abs_typed_vm_agreement : forall prim (balance : Z),
  run prim 4 (erase_program fa12_dup_abs_typed)
    (erase_stack [MInt] (balance,tt)) =
  Some (erase_stack [MNat;MInt;MInt] (execute_program fa12_dup_abs_typed (balance,tt))).
Proof. intros. apply typed_program_erasure_simulates_vm. Qed.
Print Assumptions fa12_dup_abs_typed_vm_agreement.
