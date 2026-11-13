From Coq Require Import List ZArith String.
Require Import FullVM_WIP FA12LoopBody.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* Exact FA1.2 initialization and post-loop programs in the partial VM.
   This packages deferred operations, not their later execution. The whole
   script theorem requires a separately proved iteration equation; the mixed
   trace theorem can discharge it. AMOUNT/typed CONTRACT lookup, the source
   translation, gas, typing and Octez correspondence remain external. *)
Section Boundary.
  Variable primitive : string -> stack -> option stack.
  Variable amount : nat.
  Variable contract_lookup : value -> option value.
  Definition option_contract (c : option value) := match c with None => VNone | Some h => VSome h end.
  Hypothesis amount_frame : forall s, primitive "AMOUNT" s = Some (VMutez amount :: s).
  Hypothesis contract_frame : forall token rest,
    primitive "CONTRACT_FA12_TRANSFER" (token :: rest) = Some (option_contract (contract_lookup token) :: rest).

  Definition lookup_code : list instruction :=
    [Dup 1; Prim "CONTRACT_FA12_TRANSFER"; IfNone FA12LoopBody.fail []].
  Definition init_after_amount : list instruction :=
    [Push (VMutez 0); CompareInt; IsEq; If [] FA12LoopBody.fail; UnpairN 3; Dip 2 lookup_code].
  Definition init_code : list instruction :=
    [Nil; Nil; Pair; Swap; Prim "AMOUNT"] ++ init_after_amount.
  Definition reverse_code : list instruction := [Nil; Swap; Iter [Cons]].
  Definition merge_code : list instruction := [Iter [Cons]; PairN 3].
  Definition final_code : list instruction := [Swap; Drop; Dig 2; Unpair; Dip 1 reverse_code] ++ merge_code.
  Definition full_code : list instruction := init_code ++ Iter FA12LoopBody.iteration :: final_code.

  Lemma init_amount_step : forall fuel tail txs state token frame,
    run primitive (5 + fuel)%nat (init_code ++ tail)
      (VPair (VList txs) (VPair state token) :: frame) =
    match primitive "AMOUNT"
      (VPair (VList txs) (VPair state token) :: VPair (VList []) (VList []) :: frame) with
    | Some s => run primitive fuel (init_after_amount ++ tail) s | None => None end.
  Proof. reflexivity. Qed.
  Lemma init_lookup_step : forall fuel tail txs state token frame,
    run primitive (6 + S fuel)%nat (init_after_amount ++ tail)
      (VMutez 0 :: VPair (VList txs) (VPair state token) :: VPair (VList []) (VList []) :: frame) =
    match (match run primitive (S fuel) lookup_code
      (token :: VPair (VList []) (VList []) :: frame) with
      | Some s => Some (VList txs :: state :: s) | None => None end) with
    | Some s => run primitive (S fuel) tail s | None => None end.
  Proof. reflexivity. Qed.
  Lemma lookup_prefix_step : forall fuel token rest,
    run primitive (2 + fuel)%nat lookup_code (token :: rest) =
    match primitive "CONTRACT_FA12_TRANSFER" (token :: token :: rest) with
    | Some s => run primitive fuel [IfNone FA12LoopBody.fail []] s | None => None end.
  Proof. reflexivity. Qed.
  Lemma lookup_some_step : forall fuel handle rest,
    run primitive (3 + fuel)%nat [IfNone FA12LoopBody.fail []] (VSome handle :: rest) = Some (handle :: rest).
  Proof. reflexivity. Qed.
  Lemma lookup_none_step : forall fuel rest,
    run primitive (4 + fuel)%nat [IfNone FA12LoopBody.fail []] (VNone :: rest) = None.
  Proof. reflexivity. Qed.
  Lemma nonzero_amount_step : forall fuel n tail txs state token frame,
    run primitive (8 + fuel)%nat (init_after_amount ++ tail)
      (VMutez (S n) :: VPair (VList txs) (VPair state token) :: VPair (VList []) (VList []) :: frame) = None.
  Proof. reflexivity. Qed.

  Lemma cons_step : forall fuel x xs rest,
    run primitive (2 + fuel)%nat [Cons] (x :: VList xs :: rest) = Some (VList (x :: xs) :: rest).
  Proof. reflexivity. Qed.
  Lemma iterate_cons : forall fuel xs acc rest,
    iterate (fun x s => run primitive (2 + fuel)%nat [Cons] (x :: s)) xs (VList acc :: rest) =
    Some (VList (rev xs ++ acc) :: rest).
  Proof.
    intros fuel xs. induction xs as [|x xs IH]; intros acc rest; cbn [iterate].
    - reflexivity.
    - rewrite cons_step, IH. cbn [rev]. rewrite <- app_assoc. reflexivity.
  Qed.
  Lemma reverse_prefix_step : forall fuel xs rest,
    run primitive (5 + fuel)%nat reverse_code (VList xs :: rest) =
    match iterate (fun x s => run primitive (2 + fuel)%nat [Cons] (x :: s)) xs (VList [] :: rest) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Lemma final_prefix_step : forall fuel state handle token ds ws frame,
    run primitive (5 + fuel)%nat final_code
      (state :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match run primitive fuel reverse_code (VList ws :: state :: token :: frame) with
    | Some s => run primitive fuel merge_code (VList ds :: s) | None => None end.
  Proof.
    intros. cbn [final_code run Nat.add List.app List.length nth_error firstn skipn Nat.leb].
    destruct (run primitive fuel reverse_code (VList ws :: state :: token :: frame)); reflexivity.
  Qed.
  Lemma merge_prefix_step : forall fuel ds ws state token frame,
    run primitive (4 + fuel)%nat merge_code
      (VList ds :: VList ws :: state :: token :: frame) =
    match iterate (fun x s => run primitive (3 + fuel)%nat [Cons] (x :: s)) ds
      (VList ws :: state :: token :: frame) with
    | Some s => run primitive (3 + fuel)%nat [PairN 3] s | None => None end.
  Proof. reflexivity. Qed.
  Lemma loop_prefix_step : forall fuel txs initial,
    run primitive (S fuel) (Iter FA12LoopBody.iteration :: final_code) (VList txs :: initial) =
    match iterate (fun tx s => run primitive fuel FA12LoopBody.iteration (tx :: s)) txs initial with
    | Some s => run primitive fuel final_code s | None => None end.
  Proof. reflexivity. Qed.
  Lemma nil_step : forall fuel s, run primitive (S fuel) [] s = Some s.
  Proof. reflexivity. Qed.
  Lemma pair_three_final_step : forall fuel ops state token frame,
    run primitive (3 + fuel)%nat [PairN 3] (VList ops :: state :: token :: frame) =
    Some (VPair (VList ops) (VPair state token) :: frame).
  Proof. reflexivity. Qed.
  Local Opaque run.

  Theorem lookup_passes : forall padding token handle rest,
    contract_lookup token = Some handle ->
    run primitive (5 + padding)%nat lookup_code (token :: rest) = Some (handle :: token :: rest).
  Proof.
    intros padding token handle rest HC.
    rewrite (lookup_prefix_step (3 + padding)%nat), contract_frame, HC.
    apply (lookup_some_step padding).
  Qed.
  Theorem lookup_rejects : forall padding token rest,
    contract_lookup token = None -> run primitive (6 + padding)%nat lookup_code (token :: rest) = None.
  Proof.
    intros padding token rest HC.
    rewrite (lookup_prefix_step (4 + padding)%nat), contract_frame, HC.
    apply (lookup_none_step padding).
  Qed.
  Theorem initializes_exact_stack : forall txs state token handle frame,
    amount = 0%nat -> contract_lookup token = Some handle ->
    run primitive 64 init_code (VPair (VList txs) (VPair state token) :: frame) =
    Some (VList txs :: state :: handle :: token :: VPair (VList []) (VList []) :: frame).
  Proof.
    intros txs state token handle frame HA HC.
    rewrite <- (app_nil_r init_code).
    rewrite (init_amount_step 59), amount_frame, HA, (init_lookup_step 52).
    rewrite (lookup_passes 48 token handle) by exact HC. apply (nil_step 52).
  Qed.
  Theorem init_rejects_nonzero_amount : forall n txs state token frame,
    amount = S n -> run primitive 64 init_code (VPair (VList txs) (VPair state token) :: frame) = None.
  Proof.
    intros n txs state token frame HA.
    rewrite <- (app_nil_r init_code).
    rewrite (init_amount_step 59), amount_frame, HA. apply (nonzero_amount_step 51).
  Qed.
  Theorem init_rejects_missing_interface : forall txs state token frame,
    amount = 0%nat -> contract_lookup token = None ->
    run primitive 64 init_code (VPair (VList txs) (VPair state token) :: frame) = None.
  Proof.
    intros txs state token frame HA HC.
    rewrite <- (app_nil_r init_code).
    rewrite (init_amount_step 59), amount_frame, HA, (init_lookup_step 52).
    rewrite (lookup_rejects 47 token) by exact HC. reflexivity.
  Qed.

  Theorem reverse_exact : forall padding xs rest,
    run primitive (5 + padding)%nat reverse_code (VList xs :: rest) = Some (VList (rev xs) :: rest).
  Proof. intros; rewrite reverse_prefix_step, iterate_cons, app_nil_r; reflexivity. Qed.
  Theorem merge_exact : forall padding ds ws state token frame,
    run primitive (4 + padding)%nat merge_code
      (VList (rev ds) :: VList ws :: state :: token :: frame) =
    Some (VPair (VList (ds ++ ws)) (VPair state token) :: frame).
  Proof.
    intros padding ds ws state token frame.
    rewrite (merge_prefix_step padding), (iterate_cons (1 + padding)%nat), rev_involutive.
    apply (pair_three_final_step padding).
  Qed.
  Theorem final_code_exact : forall padding state handle token deposits withdrawals frame,
    run primitive (14 + padding)%nat final_code
      (state :: handle :: token :: VPair (VList (rev deposits)) (VList (rev withdrawals)) :: frame) =
    Some (VPair (VList (deposits ++ withdrawals)) (VPair state token) :: frame).
  Proof.
    intros padding state handle token deposits withdrawals frame.
    rewrite (final_prefix_step (9 + padding)%nat), (reverse_exact (4 + padding)%nat), rev_involutive.
    apply (merge_exact (5 + padding)%nat).
  Qed.

  Theorem full_contract_from_iteration : forall txs old token handle next deposits withdrawals frame,
    amount = 0%nat -> contract_lookup token = Some handle ->
    iterate (fun tx s => run primitive 128 FA12LoopBody.iteration (tx :: s)) txs
      (old :: handle :: token :: VPair (VList []) (VList []) :: frame) =
    Some (next :: handle :: token :: VPair (VList (rev deposits)) (VList (rev withdrawals)) :: frame) ->
    run primitive 140 full_code (VPair (VList txs) (VPair old token) :: frame) =
    Some (VPair (VList (deposits ++ withdrawals)) (VPair next token) :: frame).
  Proof.
    intros txs old token handle next deposits withdrawals frame HA HC HL.
    unfold full_code. rewrite (init_amount_step 135), amount_frame, HA, (init_lookup_step 128).
    rewrite (lookup_passes 124 token handle) by exact HC.
    rewrite (loop_prefix_step 128), HL. apply (final_code_exact 114).
  Qed.
End Boundary.

Print Assumptions initializes_exact_stack.
Print Assumptions init_rejects_nonzero_amount.
Print Assumptions init_rejects_missing_interface.
Print Assumptions final_code_exact.
Print Assumptions full_contract_from_iteration.
