From Coq Require Import List String ZArith.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(* Exact modeled source prefixes/suffixes. The nonprivate arm is a parameter:
   this module does not prove the token-operation construction in that arm. *)
Definition zero_tez_guard : list instruction :=
  [Prim "AMOUNT"; Push (VMutez 0); CompareInt; IsEq; If [] [Unit; Fail]].
Definition initialize : list instruction :=
  [UnpairN 4; Nil; Dug 2; EmptyMap; Dug 2].
Definition private_post (nonprivate : list instruction) : list instruction :=
  [Dup 2; Size; Dup 4; Size; Add; Push (VNat 0); CompareInt; IsEq;
   If [Dip 1 [DropN 2]; PairN 3; Nil; Pair] nonprivate].

Section Boundary.
  Variable prim : string -> stack -> option stack.
  Variable amount : nat.
  Hypothesis amount_frame : forall s, prim "AMOUNT" s = Some (VMutez amount :: s).

  Lemma amount_step : forall fuel s,
    run prim (S fuel) zero_tez_guard s =
    match prim "AMOUNT" s with
    | Some next => run prim fuel [Push (VMutez 0); CompareInt; IsEq; If [] [Unit; Fail]] next
    | None => None
    end.
  Proof. reflexivity. Qed.
  Lemma zero_tez_accepts : forall s,
    amount = 0%nat -> run prim 12 zero_tez_guard s = Some s.
  Proof.
    intros s H; rewrite (amount_step 11), amount_frame, H. reflexivity.
  Qed.
  Lemma nonzero_tez_rejects : forall s,
    amount <> 0%nat -> run prim 12 zero_tez_guard s = None.
  Proof.
    intros s H; destruct amount as [|n]; [contradiction|].
    rewrite (amount_step 11), amount_frame. reflexivity.
  Qed.
  Lemma initializes_exact_stacks : forall txs state token id frame,
    run prim 12 initialize
      (VPair (VList txs) (VPair state (VPair token id)) :: frame) =
    Some (VList txs :: state :: VMap [] :: VList [] :: token :: id :: frame).
  Proof. reflexivity. Qed.
  Lemma private_only_returns_no_operations : forall nonprivate state token id frame,
    run prim 24 (private_post nonprivate)
      (state :: VMap [] :: VList [] :: token :: id :: frame) =
    Some (VPair (VList []) (VPair state (VPair token id)) :: frame).
  Proof. reflexivity. Qed.
End Boundary.
Print Assumptions zero_tez_accepts.
Print Assumptions nonzero_tez_rejects.
Print Assumptions initializes_exact_stacks.
Print Assumptions private_only_returns_no_operations.
