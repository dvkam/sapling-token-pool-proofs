From Coq Require Import List ZArith String.
Import ListNotations.
Open Scope Z_scope.

(* WORK IN PROGRESS: this is a partial modeled semantics, connected to parsed
   scripts by a trusted translator, not a proved semantics of Michelson. Failures and absent behavior are represented by None; gas,
   types, crypto, operations, tickets, rollback and packing are NOT modeled.
   No theorem about a contract should use this VM until correspondence lemmas
   and precise primitive specifications have been proved or stated. *)
Inductive value :=
| VInt (z : Z) | VNat (n : nat) | VMutez (n : nat) | VBool (b : bool) | VUnit | VPair (a b : value)
| VSome (x : value) | VNone | VList (xs : list value) | VBytes (xs : list nat)
| VString (xs : list nat) | VMap (entries : list (value * value))
| VTicket (ticketer contents : value) (amount : nat) | VOpaque (tag : nat).

Inductive instruction :=
| Drop | DropN (n : nat) | Dup (n : nat) | Swap | Dig (n : nat) | Dug (n : nat)
| Pair | PairN (n : nat) | Unpair | UnpairN (n : nat) | Car | Cdr | ReadTicket | Nil | EmptyMap | Cons | Push (v : value) | Unit | SomeValue | NoneValue | Size | ToInt | IsNat | Add | Sub | Abs
| IsEq | IsGt | IsLt | CompareInt
| If (yes no : list instruction) | IfNone (none some : list instruction)
| Dip (n : nat) (body : list instruction) | Iter (body : list instruction) | Map (body : list instruction)
| Prim (name : string) | Fail.

Definition stack := list value.
Fixpoint pair_n (n : nat) (s : stack) : option stack :=
  match n, s with
  | 2%nat, a :: b :: rest => Some (VPair a b :: rest)
  | S (S (S k)), a :: rest =>
      match pair_n (S (S k)) rest with Some (b :: tail) => Some (VPair a b :: tail) | _ => None end
  | _, _ => None
  end.
Fixpoint unpair_n (n : nat) (v : value) : option (list value) :=
  match n with
  | O => None
  | 1%nat => Some [v]
  | S n' => match v with
      | VPair a b => match unpair_n n' b with Some xs => Some (a :: xs) | None => None end
      | _ => None end
  end.
Fixpoint iterate (action : value -> stack -> option stack) (xs : list value) (acc : stack) : option stack :=
  match xs with
  | [] => Some acc
  | x :: xs' => match action x acc with Some next => iterate action xs' next | None => None end
  end.

Section Interpreter.
  Variable primitive : string -> stack -> option stack.

  (* Fuel controls nesting/sequence execution. Iteration over the input list
     is structurally recursive and each body invocation reuses the same
     subfuel, so batch length is not bounded by this fuel. *)
  Fixpoint run (fuel : nat) (code : list instruction) (s : stack) : option stack :=
    match fuel with
    | O => None
    | S f =>
      match code with
      | [] => Some s
      | i :: tail =>
        let next :=
          match i, s with
          | Drop, _ :: rest => Some rest
          | DropN n, _ => if Nat.leb n (List.length s) then Some (skipn n s) else None
          | Dup n, _ => match nth_error s (Nat.pred n) with Some x => Some (x :: s) | None => None end
          | Swap, a :: b :: rest => Some (b :: a :: rest)
          | Dig n, _ => match nth_error s n with
              | Some x => Some (x :: firstn n s ++ skipn (S n) s)
              | None => None end
          | Dug n, x :: rest =>
              if Nat.leb n (List.length rest) then Some (firstn n rest ++ x :: skipn n rest) else None
          | Pair, a :: b :: rest => Some (VPair a b :: rest)
          | PairN n, _ => pair_n n s
          | Unpair, VPair a b :: rest => Some (a :: b :: rest)
          | UnpairN n, v :: rest => match unpair_n n v with Some xs => Some (xs ++ rest) | None => None end
          | Car, VPair a _ :: rest => Some (a :: rest)
          | Cdr, VPair _ b :: rest => Some (b :: rest)
          | ReadTicket, VTicket ticketer contents amount :: rest =>
              Some (VPair ticketer (VPair contents (VNat amount)) :: VTicket ticketer contents amount :: rest)
          | Nil, _ => Some (VList [] :: s)
          | EmptyMap, _ => Some (VMap [] :: s)
          | Cons, x :: VList xs :: rest => Some (VList (x :: xs) :: rest)
          | Push v, _ => Some (v :: s)
          | Unit, _ => Some (VUnit :: s)
          | SomeValue, x :: rest => Some (VSome x :: rest)
          | NoneValue, _ => Some (VNone :: s)
          | Size, VList xs :: rest => Some (VNat (List.length xs) :: rest)
          | Size, VBytes xs :: rest => Some (VNat (List.length xs) :: rest)
          | Size, VString xs :: rest => Some (VNat (List.length xs) :: rest)
          | Size, VMap entries :: rest => Some (VNat (List.length entries) :: rest)
          | ToInt, VNat n :: rest => Some (VInt (Z.of_nat n) :: rest)
          | IsNat, VInt z :: rest => Some ((if Z.ltb z 0 then VNone else VSome (VNat (Z.to_nat z))) :: rest)
          | Add, VInt a :: VInt b :: rest => Some (VInt (a + b) :: rest)
          | Add, VNat a :: VNat b :: rest => Some (VNat (a + b)%nat :: rest)
          | Sub, VInt a :: VInt b :: rest => Some (VInt (a - b) :: rest)
          | Sub, VNat a :: VNat b :: rest => Some (VInt (Z.of_nat a - Z.of_nat b) :: rest)
          | Abs, VInt a :: rest => Some (VNat (Z.to_nat (Z.abs a)) :: rest)
          | IsEq, VInt a :: rest => Some (VBool (Z.eqb a 0) :: rest)
          | IsGt, VInt a :: rest => Some (VBool (Z.gtb a 0) :: rest)
          | IsLt, VInt a :: rest => Some (VBool (Z.ltb a 0) :: rest)
          | CompareInt, VInt a :: VInt b :: rest =>
              Some (VInt (match Z.compare a b with Lt => -1 | Eq => 0 | Gt => 1 end) :: rest)
          | CompareInt, VNat a :: VNat b :: rest =>
              Some (VInt (match Nat.compare a b with Lt => -1 | Eq => 0 | Gt => 1 end) :: rest)
          | CompareInt, VMutez a :: VMutez b :: rest =>
              Some (VInt (match Nat.compare a b with Lt => -1 | Eq => 0 | Gt => 1 end) :: rest)
          | If yes no, VBool b :: rest => run f (if b then yes else no) rest
          | IfNone none some, VNone :: rest => run f none rest
          | IfNone none some, VSome x :: rest => run f some (x :: rest)
          | Dip n body, _ =>
              if Nat.leb n (List.length s) then
                match run f body (skipn n s) with Some out => Some (firstn n s ++ out) | None => None end
              else None
          | Iter body, VList xs :: rest =>
              iterate (fun x acc => run f body (x :: acc)) xs rest
          (* The entries are already in the order supplied by the caller.
             Sorted/unique keys and correspondence to Michelson maps are
             external obligations, not enforced by this untyped model. *)
          | Iter body, VMap entries :: rest =>
              iterate (fun x acc => run f body (x :: acc))
                (List.map (fun entry => VPair (fst entry) (snd entry)) entries) rest
          | Map body, VList xs :: rest =>
              let fix map_items (xs : list value) (acc : stack) : option (list value * stack) :=
                match xs with
                | [] => Some ([], acc)
                | x :: xs' =>
                    match run f body (x :: acc) with
                    | Some (y :: next) =>
                        match map_items xs' next with
                        | Some (ys, final) => Some (y :: ys, final)
                        | None => None end
                    | _ => None end
                end in
              match map_items xs rest with
              | Some (ys, final) => Some (VList ys :: final)
              | None => None end
          | Prim name, _ => primitive name s
          | _, _ => None
          end in
        match next with Some s' => run f tail s' | None => None end
      end
    end.

  (* Engineering sanity check only: a fixed amount of structural fuel can
     execute a modeled drop-body on lists of arbitrary length. *)
  Theorem iter_drop_fixed_fuel : forall xs s,
    run 4 [Iter [Drop]] (VList xs :: s) = Some s.
  Proof.
    induction xs as [|x xs IH]; intros s; cbn [run iterate] in *.
    - reflexivity.
    - exact (IH s).
  Qed.

  Theorem comb_pair_three_roundtrip : forall a b c rest,
    run 4 [PairN 3; UnpairN 3] (a :: b :: c :: rest) = Some (a :: b :: c :: rest).
  Proof. reflexivity. Qed.

  Lemma iter_cons_accumulator : forall xs acc rest,
    iterate (fun x st => run 5 [Cons] (x :: st)) xs (VList acc :: rest) =
      Some (VList (rev xs ++ acc) :: rest).
  Proof.
    induction xs as [|x xs IH]; intros acc rest; cbn [iterate run].
    - reflexivity.
    - rewrite IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
  Qed.

  Theorem source_reverse_fixed_fuel : forall xs rest,
    run 8 [Nil; Swap; Iter [Cons]] (VList xs :: rest) =
      Some (VList (rev xs) :: rest).
  Proof.
    intros xs rest. cbn [run]. rewrite iter_cons_accumulator, app_nil_r. reflexivity.
  Qed.
End Interpreter.
