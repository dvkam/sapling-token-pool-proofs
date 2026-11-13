(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String ZArith Lia.
Require Import FullVM_WIP FA2Boundary FA2Combined FA2Environment FA2MixedBatch
  FA2PrivateSuccess FA2Operations FA2Map FA2MapFuel FA12Boundary FA2DepositFuel.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Exact parsed public arm under the checker's source equality. Successful trace -> modeled
   operation construction only: no map laws, token execution or safety converse. *)
Definition public_finish : list instruction :=
  [Push (VMutez 0); Swap; Prim "TRANSFER_TOKENS"; Nil; Swap; Cons; PairN 4].
Definition public_after_self : list instruction :=
  [Pair; Cons; Nil; Swap; Iter [Cons]] ++ public_finish.
Definition public_after_map : list instruction := Prim "SELF_ADDRESS" :: public_after_self.
Definition public_after_reverse : list instruction := Map withdrawal_item_body :: public_after_map.
Definition public_after_deposits : list instruction :=
  [Dig 3; Nil; Swap; Iter [Cons]] ++ public_after_reverse.
Definition public_after_lookup : list instruction :=
  [IfNone [Unit; Fail] []; Nil; Dig 3; Iter deposit_group_body] ++ public_after_deposits.
Definition public_code : list instruction :=
  [Dup 4; Prim "CONTRACT_FA2_TRANSFER"] ++ public_after_lookup.
Definition full_code : list instruction := FA2PrivateSuccess.full_private_code public_code.
Definition pair_entries (xs : list (value * value)) :=
  List.map (fun entry => VPair (fst entry) (snd entry)) xs.
Definition withdrawal_items (id : value) (xs : list (value * value)) :=
  List.map (fun entry => VPair (fst entry) (VPair id (snd entry))) xs.
Definition transfer_groups (pool id : value) (entries withdrawals : list (value * value)) :=
  List.map (fun entry => deposit_group pool id (fst entry) (snd entry)) entries ++
  [VPair pool (VList (withdrawal_items id withdrawals))].

Lemma reverse_pair_entries : forall xs, rev (pair_entries (rev xs)) = pair_entries xs.
Proof. intros; unfold pair_entries; rewrite <- map_rev, rev_involutive; reflexivity. Qed.
Lemma final_groups_order : forall pool id entries outgoing,
  rev (outgoing :: reverse_deposit_groups pool entries [] id) =
  List.map (fun entry => deposit_group pool id (fst entry) (snd entry)) entries ++ [outgoing].
Proof.
  intros. cbn [rev]. rewrite deposit_groups_reverse_entries, app_nil_r, rev_involutive.
  reflexivity.
Qed.

Section Public.
  Variable prim : string -> stack -> option stack.
  Variable pool : value.
  Variable operation : value -> value -> value.
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (pool :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) =
    Some (operation parameter handle :: rest).

  Lemma lookup_prefix : forall fuel state entries ws token id frame,
    run prim (2 + fuel)%nat public_code
      (state :: VMap entries :: VList ws :: token :: id :: frame) =
    match prim "CONTRACT_FA2_TRANSFER" (token :: state :: VMap entries :: VList ws :: token :: id :: frame) with
    | Some s => run prim fuel public_after_lookup s | None => None end.
  Proof. reflexivity. Qed.

  Lemma deposit_prefix : forall fuel state entries ws token id handle frame,
    run prim (4 + fuel)%nat public_after_lookup
      (VSome handle :: state :: VMap entries :: VList ws :: token :: id :: frame) =
    match iterate (fun x s => run prim fuel deposit_group_body (x :: s))
      (pair_entries entries) (VList [] :: handle :: state :: VList ws :: token :: id :: frame) with
    | Some s => run prim fuel public_after_deposits s | None => None end.
  Proof. reflexivity. Qed.

  Lemma withdrawal_reverse_prefix : forall fuel groups state ws token id handle frame,
    run prim (4 + fuel)%nat public_after_deposits
      (VList groups :: handle :: state :: VList ws :: token :: id :: frame) =
    match iterate (fun x s => run prim fuel [Cons] (x :: s)) ws
      (VList [] :: VList groups :: handle :: state :: token :: id :: frame) with
    | Some s => run prim fuel public_after_reverse s | None => None end.
  Proof. reflexivity. Qed.

  Lemma withdrawal_map_prefix : forall fuel xs rest,
    run prim (S (S fuel)) public_after_reverse (VList xs :: rest) =
    match FA2Map.map_items prim (S fuel) xs rest with
    | Some (ys, next) => run prim (S fuel) public_after_map (VList ys :: next)
    | None => None end.
  Proof.
    intros. change (
      match (match FA2Map.local_items prim (S fuel) xs rest with
        | Some (ys, next) => Some (VList ys :: next) | None => None end) with
      | Some s => run prim (S fuel) public_after_map s | None => None end =
      match FA2Map.map_items prim (S fuel) xs rest with
      | Some (ys, next) => run prim (S fuel) public_after_map (VList ys :: next)
      | None => None end).
    rewrite FA2Map.local_items_match.
    destruct (FA2Map.map_items prim (S fuel) xs rest) as [[ys next]|]; reflexivity.
  Qed.

  Lemma self_prefix : forall fuel s,
    run prim (S fuel) public_after_map s =
    match prim "SELF_ADDRESS" s with
    | Some next => run prim fuel public_after_self next | None => None end.
  Proof. reflexivity. Qed.

  Lemma group_reverse_prefix : forall fuel items groups handle state token id frame,
    run prim (5 + fuel)%nat public_after_self
      (pool :: VList items :: VList groups :: handle :: state :: token :: id :: frame) =
    match iterate (fun x s => run prim fuel [Cons] (x :: s))
      (VPair pool (VList items) :: groups)
      (VList [] :: handle :: state :: token :: id :: frame) with
    | Some s => run prim fuel public_finish s | None => None end.
  Proof. reflexivity. Qed.

  Lemma transfer_prefix : forall fuel groups handle state token id frame,
    run prim (3 + fuel)%nat public_finish
      (VList groups :: handle :: state :: token :: id :: frame) =
    match prim "TRANSFER_TOKENS" (VList groups :: VMutez 0 :: handle :: state :: token :: id :: frame) with
    | Some s => run prim fuel [Nil; Swap; Cons; PairN 4] s | None => None end.
  Proof. reflexivity. Qed.

  Lemma returns_exact_storage : forall fuel op state token id frame,
    run prim (5 + fuel)%nat [Nil; Swap; Cons; PairN 4]
      (op :: state :: token :: id :: frame) =
    Some (VPair (VList [op]) (VPair state (VPair token id)) :: frame).
  Proof. reflexivity. Qed.

  Local Opaque run.

  Theorem public_arm_constructs_ordered_transfer : forall state entries withdrawals token id handle frame,
    (forall rest, prim "CONTRACT_FA2_TRANSFER" (token :: rest) = Some (VSome handle :: rest)) ->
    run prim 119 public_code
      (state :: VMap entries :: VList (pair_entries (rev withdrawals)) :: token :: id :: frame) =
    Some (VPair (VList [operation (VList (transfer_groups pool id entries withdrawals)) handle])
      (VPair state (VPair token id)) :: frame).
  Proof.
    intros state entries withdrawals token id handle frame HC.
    rewrite (lookup_prefix 117), HC, (deposit_prefix 113).
    unfold pair_entries at 1.
    rewrite (FA2DepositFuel.deposit_iterate_fuel prim pool self_frame 101).
    rewrite (withdrawal_reverse_prefix 109), (FA12Boundary.iterate_cons prim 107), app_nil_r.
    rewrite reverse_pair_entries, (withdrawal_map_prefix 107).
    unfold pair_entries.
    rewrite (FA2MapFuel.mapped_items_exact_fuel 103), (self_prefix 107), self_frame.
    rewrite (group_reverse_prefix 102), (FA12Boundary.iterate_cons prim 100), app_nil_r.
    rewrite final_groups_order, (transfer_prefix 99), transfer_frame.
    apply (returns_exact_storage 94).
  Qed.
End Public.

Print Assumptions public_arm_constructs_ordered_transfer.

Section Complete.
  Variable prim : string -> stack -> option stack.
  Variable pool : value.
  Variable operation : value -> value -> value.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez 0 :: rest).
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (pool :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) =
    Some (operation parameter handle :: rest).

  Lemma post_guard_prefix : forall fuel state entries ws token id frame,
    run prim (8 + fuel)%nat (FA2Boundary.private_post public_code)
      (state :: VMap entries :: VList ws :: token :: id :: frame) =
    run prim fuel
      [If [Dip 1 [DropN 2]; PairN 3; Nil; Pair] public_code]
      (VBool (Z.eqb (match Nat.compare 0 (List.length ws + List.length entries)%nat with
        Lt => -1 | Eq => 0 | Gt => 1 end) 0) ::
       state :: VMap entries :: VList ws :: token :: id :: frame).
  Proof. reflexivity. Qed.

  Lemma select_public : forall fuel s,
    run prim (S (S fuel))
      [If [Dip 1 [DropN 2]; PairN 3; Nil; Pair] public_code] (VBool false :: s) =
    run prim (S fuel) public_code s.
  Proof.
    intros. change ((match run prim (S fuel) public_code s with
      Some out => Some out | None => None end) = run prim (S fuel) public_code s).
    destruct (run prim (S fuel) public_code s); reflexivity.
  Qed.

  Lemma nonempty_post_selects_public : forall state entries ws token id frame,
    (List.length ws + List.length entries <> 0)%nat ->
    run prim 128 (FA2Boundary.private_post public_code)
      (state :: VMap entries :: VList ws :: token :: id :: frame) =
    run prim 119 public_code (state :: VMap entries :: VList ws :: token :: id :: frame).
  Proof.
    intros state entries ws token id frame H.
    rewrite (post_guard_prefix 120).
    destruct ws as [|w ws]; destruct entries as [|e entries].
    - exfalso; apply H; reflexivity.
    - change (run prim 120
        [If [Dip 1 [DropN 2]; PairN 3; Nil; Pair] public_code]
        (VBool false :: state :: VMap (e :: entries) :: VList [] :: token :: id :: frame) =
        run prim 119 public_code (state :: VMap (e :: entries) :: VList [] :: token :: id :: frame)).
      apply select_public.
    - change (run prim 120
        [If [Dip 1 [DropN 2]; PairN 3; Nil; Pair] public_code]
        (VBool false :: state :: VMap [] :: VList (w :: ws) :: token :: id :: frame) =
        run prim 119 public_code (state :: VMap [] :: VList (w :: ws) :: token :: id :: frame)).
      apply select_public.
    - change (run prim 120
        [If [Dip 1 [DropN 2]; PairN 3; Nil; Pair] public_code]
        (VBool false :: state :: VMap (e :: entries) :: VList (w :: ws) :: token :: id :: frame) =
        run prim 119 public_code (state :: VMap (e :: entries) :: VList (w :: ws) :: token :: id :: frame)).
      apply select_public.
  Qed.

  Local Opaque run.
  Theorem full_public_from_iteration : forall txs old next entries withdrawals token id handle frame,
    (forall rest, prim "CONTRACT_FA2_TRANSFER" (token :: rest) = Some (VSome handle :: rest)) ->
    (List.length entries + List.length withdrawals <> 0)%nat ->
    iterate (fun tx s => run prim 128 FA2Combined.canonical_iteration (tx :: s)) txs
      (old :: VMap [] :: VList [] :: token :: id :: frame) =
    Some (next :: VMap entries :: VList (pair_entries (rev withdrawals)) :: token :: id :: frame) ->
    run prim 139 full_code
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) =
    Some (VPair (VList [operation (VList (transfer_groups pool id entries withdrawals)) handle])
      (VPair next (VPair token id)) :: frame).
  Proof.
    intros txs old next entries withdrawals token id handle frame HC HN HI.
    unfold full_code, FA2PrivateSuccess.full_private_code.
    rewrite (FA2PrivateSuccess.guard_step prim 138), amount_frame,
      (FA2PrivateSuccess.guard_pass prim 133), (FA2PrivateSuccess.init_step prim 129),
      (FA2PrivateSuccess.loop_step prim 127), HI.
    rewrite nonempty_post_selects_public.
    - eapply public_arm_constructs_ordered_transfer; eauto.
    - unfold pair_entries. rewrite map_length, rev_length. lia.
  Qed.
End Complete.

Section MixedComplete.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable other : string -> stack -> option stack.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.
  Variable pool : value.
  Variable operation : value -> value -> value.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez 0 :: rest).
  Hypothesis self_frame : forall rest, prim "SELF_ADDRESS" rest = Some (pool :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) =
    Some (operation parameter handle :: rest).

  Theorem whole_public_successful_mixed_trace : forall txs old next entries withdrawals token id handle frame,
    (forall rest, prim "CONTRACT_FA2_TRANSFER" (token :: rest) = Some (VSome handle :: rest)) ->
    (List.length entries + List.length withdrawals <> 0)%nat ->
    FA2MixedBatch.mixed_trace verify unpack pack sender lookup update txs old (VMap []) []
      next (VMap entries) (pair_entries (rev withdrawals)) ->
    run prim 139 full_code
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) =
    Some (VPair (VList [operation (VList (transfer_groups pool id entries withdrawals)) handle])
      (VPair next (VPair token id)) :: frame).
  Proof.
    intros txs old next entries withdrawals token id handle frame HC HN HT.
    eapply (full_public_from_iteration prim pool operation amount_frame self_frame transfer_frame); eauto.
    eapply FA2MixedBatch.mixed_trace_iterates; eauto.
  Qed.
End MixedComplete.

Print Assumptions full_public_from_iteration.
Print Assumptions whole_public_successful_mixed_trace.
