From Coq Require Import List String ZArith.
Require Import FullVM_WIP FA2Boundary FA2Combined FA2Environment FA2MixedBatch.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Whole modeled FA2 private-output successful calls only. The public arm is
   parameterized and not executed; translator/primitive semantics are trusted. *)
Definition full_private_code (nonprivate : list instruction) :=
  FA2Boundary.zero_tez_guard ++ FA2Boundary.initialize ++
  Iter FA2Combined.canonical_iteration :: FA2Boundary.private_post nonprivate.

Section Private.
  Variable prim : string -> stack -> option stack.
  Hypothesis amount_frame : forall s, prim "AMOUNT" s = Some (VMutez 0 :: s).

  Lemma guard_step : forall fuel tail s,
    run prim (S fuel) (FA2Boundary.zero_tez_guard ++ tail) s =
    match prim "AMOUNT" s with
    | Some next => run prim fuel ([Push (VMutez 0); CompareInt; IsEq; If [] [Unit;Fail]] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.
  Lemma guard_pass : forall fuel tail s,
    run prim (4 + S fuel)%nat ([Push (VMutez 0); CompareInt; IsEq; If [] [Unit;Fail]] ++ tail)
      (VMutez 0 :: s) = run prim (S fuel) tail s.
  Proof. reflexivity. Qed.
  Lemma init_step : forall fuel tail txs state token id frame,
    run prim (5 + fuel)%nat (FA2Boundary.initialize ++ tail)
      (VPair (VList txs) (VPair state (VPair token id)) :: frame) =
    run prim fuel tail (VList txs :: state :: VMap [] :: VList [] :: token :: id :: frame).
  Proof. reflexivity. Qed.
  Lemma loop_step : forall fuel tail txs state map ws token id frame,
    run prim (S (S fuel)) (Iter FA2Combined.canonical_iteration :: tail)
      (VList txs :: state :: map :: VList ws :: token :: id :: frame) =
    match iterate (fun tx s => run prim (S fuel) FA2Combined.canonical_iteration (tx :: s))
      txs (state :: map :: VList ws :: token :: id :: frame) with
    | Some out => run prim (S fuel) tail out | None => None end.
  Proof. reflexivity. Qed.
  Lemma private_post_fuel : forall fuel nonprivate state token id frame,
    run prim (24 + fuel)%nat (FA2Boundary.private_post nonprivate)
      (state :: VMap [] :: VList [] :: token :: id :: frame) =
    Some (VPair (VList []) (VPair state (VPair token id)) :: frame).
  Proof. reflexivity. Qed.

  Theorem private_full_from_iteration : forall nonprivate txs old next token id frame,
    iterate (fun tx s => run prim 128 FA2Combined.canonical_iteration (tx :: s))
      txs (old :: VMap [] :: VList [] :: token :: id :: frame) =
    Some (next :: VMap [] :: VList [] :: token :: id :: frame) ->
    run prim 139 (full_private_code nonprivate)
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) =
    Some (VPair (VList []) (VPair next (VPair token id)) :: frame).
  Proof.
    intros nonprivate txs old next token id frame H.
    unfold full_private_code.
    rewrite (guard_step 138), amount_frame, (guard_pass 133).
    rewrite (init_step 129), (loop_step 127), H.
    apply (private_post_fuel 104).
  Qed.
End Private.

Section PrivateMixed.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable other : string -> stack -> option stack.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Hypothesis amount_frame : forall s, prim "AMOUNT" s = Some (VMutez 0 :: s).

  Theorem private_full_successful_mixed_trace : forall nonprivate txs old next token id frame,
    FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
      txs old (VMap []) [] next (VMap []) [] ->
    run prim 139 (full_private_code nonprivate)
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) =
    Some (VPair (VList []) (VPair next (VPair token id)) :: frame).
  Proof.
    intros nonprivate txs old next token id frame H.
    eapply (private_full_from_iteration prim amount_frame).
    eapply FA2MixedBatch.mixed_trace_iterates; eauto.
  Qed.
End PrivateMixed.
Print Assumptions private_full_successful_mixed_trace.
(* Specialization excluding all public-balance changes; no map-update law is
   needed, because zero-balance iterations never invoke the map callback. *)
Inductive zero_trace (verify : value -> value -> option (value * Z * value)) :
  list value -> value -> value -> Prop :=
| zero_nil : forall state, zero_trace verify [] state state
| zero_cons : forall tx txs old next final,
    verify tx old = Some (VBytes [], 0, next) ->
    zero_trace verify txs next final ->
    zero_trace verify (tx :: txs) old final.

Lemma zero_trace_is_mixed : forall verify unpack pack sender lookup update txs old next,
  zero_trace verify txs old next ->
  FA2MixedBatch.mixed_trace verify unpack pack sender lookup update
    txs old (VMap []) [] next (VMap []) [].
Proof.
  intros verify unpack pack sender lookup update txs old next H.
  induction H.
  - constructor.
  - econstructor 4; eauto.
Qed.

Section ZeroPrivate.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable other : string -> stack -> option stack.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Hypothesis amount_frame : forall s, prim "AMOUNT" s = Some (VMutez 0 :: s).

  Theorem private_zero_batch : forall nonprivate txs old next token id frame,
    zero_trace verify txs old next ->
    run prim 139 (full_private_code nonprivate)
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) =
    Some (VPair (VList []) (VPair next (VPair token id)) :: frame).
  Proof.
    intros nonprivate txs old next token id frame H.
    eapply private_full_successful_mixed_trace; eauto.
    eapply zero_trace_is_mixed; eauto.
  Qed.
End ZeroPrivate.
Print Assumptions private_zero_batch.
