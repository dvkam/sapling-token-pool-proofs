From Coq Require Import List String ZArith.
Require Import FullVM_WIP FA2LoopBody FA2DepositBody FA2Combined FA2Environment LoopInduction.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* Successful traces only: each transaction has a successful abstract Sapling
   result and obeys the appropriate recipient/bound-data checks. Map operations
   are callbacks. This does not cover rejection, token calls or backing. *)
Inductive mixed_trace
  (verify : value -> value -> option (value * Z * value))
  (unpack : value -> option value) (pack : value -> list nat)
  (sender : value) (lookup : value -> value -> option nat)
  (update : value -> option nat -> value -> value) :
  list value -> value -> value -> list value -> value -> value -> list value -> Prop :=
| mixed_nil : forall state map ws, mixed_trace verify unpack pack sender lookup update [] state map ws state map ws
| mixed_positive : forall tx txs old map ws bound balance next recipient final finalmap finalws,
    verify tx old = Some (bound, balance, next) -> 0 < balance ->
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    mixed_trace verify unpack pack sender lookup update txs next map
      (VPair recipient (VNat (Z.to_nat balance)) :: ws) final finalmap finalws ->
    mixed_trace verify unpack pack sender lookup update (tx :: txs) old map ws final finalmap finalws
| mixed_negative : forall tx txs old map ws balance next final finalmap finalws,
    verify tx old = Some (VBytes [], balance, next) -> balance < 0 ->
    mixed_trace verify unpack pack sender lookup update txs next
      (update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map)
      ws final finalmap finalws ->
    mixed_trace verify unpack pack sender lookup update (tx :: txs) old map ws final finalmap finalws
| mixed_zero : forall tx txs old map ws next final finalmap finalws,
    verify tx old = Some (VBytes [], 0, next) ->
    mixed_trace verify unpack pack sender lookup update txs next map ws final finalmap finalws ->
    mixed_trace verify unpack pack sender lookup update (tx :: txs) old map ws final finalmap finalws.

Section Mixed.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable other : string -> stack -> option stack.
  Let prim := FA2Environment.primitive verify unpack pack sender lookup update other.

  Lemma positive_step128 : forall tx old bound balance next recipient map ws frame,
    verify tx old = Some (bound, balance, next) -> 0 < balance ->
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    run prim 128 FA2Combined.canonical_iteration (tx :: old :: map :: VList ws :: frame) =
    Some (next :: map :: VList (VPair recipient (VNat (Z.to_nat balance)) :: ws) :: frame).
  Proof.
    intros tx old bound balance next recipient map ws frame HV HB HU HP.
    unfold FA2Combined.canonical_iteration.
    eapply (FA2LoopBody.verified_positive_iteration_128 verify unpack pack prim).
    - intros; unfold prim; rewrite FA2Environment.unpack_frame, H; reflexivity.
    - intros; unfold prim; apply FA2Environment.pack_frame.
    - intros; unfold prim; rewrite FA2Environment.verify_frame, H; reflexivity.
    - exact HV.
    - exact HB.
    - exact HU.
    - exact HP.
  Qed.

  Lemma negative_step128 : forall tx old balance next map ws frame,
    verify tx old = Some (VBytes [], balance, next) -> balance < 0 ->
    run prim 128 FA2Combined.canonical_iteration (tx :: old :: map :: VList ws :: frame) =
    Some (next :: update sender (Some ((FA2DepositBody.balance_or_zero (lookup sender map) + Z.to_nat (Z.abs balance))%nat)) map :: VList ws :: frame).
  Proof.
    intros tx old balance next map ws frame HV HB.
    unfold FA2Combined.canonical_iteration.
    eapply (FA2DepositBody.verified_negative_iteration_128 sender lookup update prim verify).
    - intros; unfold prim; apply FA2Environment.sender_frame.
    - intros; unfold prim; rewrite FA2Environment.get_frame. destruct (lookup sender map0); reflexivity.
    - intros; unfold prim; apply FA2Environment.update_frame.
    - intros; unfold prim; rewrite FA2Environment.verify_frame, H; reflexivity.
    - exact HV.
    - exact HB.
  Qed.

  Lemma zero_step128 : forall tx old next map ws frame,
    verify tx old = Some (VBytes [], 0, next) ->
    run prim 128 FA2Combined.canonical_iteration (tx :: old :: map :: VList ws :: frame) =
    Some (next :: map :: VList ws :: frame).
  Proof.
    intros tx old next map ws frame HV.
    unfold FA2Combined.canonical_iteration.
    eapply (FA2DepositBody.verified_zero_iteration_128 prim verify).
    - intros; unfold prim; rewrite FA2Environment.verify_frame, H; reflexivity.
    - exact HV.
  Qed.

  Lemma mixed_trace_iterates : forall txs initial map ws final finalmap finalws,
    mixed_trace verify unpack pack sender lookup update txs initial map ws final finalmap finalws ->
    forall frame,
    iterate (fun tx st => run prim 128 FA2Combined.canonical_iteration (tx :: st))
      txs (initial :: map :: VList ws :: frame) =
    Some (final :: finalmap :: VList finalws :: frame).
  Proof.
    intros txs initial map ws final finalmap finalws H.
    induction H; intros frame; cbn [iterate fold_left].
    - reflexivity.
    - rewrite (positive_step128 tx old bound balance next recipient map ws frame H H0 H1 H2).
      now apply IHmixed_trace.
    - rewrite (negative_step128 tx old balance next map ws frame H H0).
      now apply IHmixed_trace.
    - rewrite (zero_step128 tx old next map ws frame H).
      now apply IHmixed_trace.
  Qed.

  Theorem unbounded_successful_mixed_batch : forall txs initial map ws final finalmap finalws,
    mixed_trace verify unpack pack sender lookup update txs initial map ws final finalmap finalws ->
    forall frame,
    run prim 129 [Iter FA2Combined.canonical_iteration]
      (VList txs :: initial :: map :: VList ws :: frame) =
    Some (final :: finalmap :: VList finalws :: frame).
  Proof.
    intros txs initial map ws final finalmap finalws H frame.
    rewrite (LoopInduction.source_loop_unbounded prim FA2Combined.canonical_iteration
      (fun tx st => run prim 128 FA2Combined.canonical_iteration (tx :: st)) 127)
      by reflexivity.
    now apply mixed_trace_iterates.
  Qed.
End Mixed.
Print Assumptions unbounded_successful_mixed_batch.
