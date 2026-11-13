(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith Lia Sorting.Permutation.
Require Import SaplingNotes.
Import ListNotations.
Open Scope Z_scope.

(* Jubjub subgroup scalar modulus, jubjub 0.9.0/src/fr.rs.
   This is NOT the BLS12-381 circuit scalar field modulus. *)
Definition jubjub_order : Z :=
  6554484396890773809930967563523245729705921265872317281365359162392183254199.
Definition note_limit : Z := 18446744073709551616. (* 2^64 *)
Definition signed_limit : Z := 9223372036854775808. (* 2^63 *)
Definition native_balance_limit : Z := 2100000000000000.
Definition bounded_notes (ns : list note) : Prop :=
  Forall (fun n => Z.of_nat (note_value n) < note_limit) ns.

Lemma bounded_note_sum : forall ns,
  bounded_notes ns ->
  0 <= liability ns <= Z.of_nat (length ns) * (note_limit - 1).
Proof.
  intros ns H; induction H; cbn [liability length].
  - lia.
  - rewrite Nat2Z.inj_succ. unfold note_limit in *; lia.
Qed.

Lemma bounded_multiple_is_zero : forall d,
  -jubjub_order < d < jubjub_order ->
  (jubjub_order | d) -> d = 0.
Proof.
  intros d HB [k HK].
  assert (HQ : 0 < jubjub_order) by (unfold jubjub_order; lia).
  destruct (Z_lt_ge_dec k 0); [nia|].
  destruct (Z.eq_dec k 0); [nia|nia].
Qed.

(* Circuit extraction supplies 64-bit witnesses. The cryptographic premise
   is only a modular value balance; integer equality is proved here. A
   signed-int64 bound is deliberately more permissive than native MAX_MONEY. *)
Theorem modular_binding_lifts_to_integer_balance : forall inputs outputs balance,
  bounded_notes inputs -> bounded_notes outputs ->
  (length inputs <= 5208)%nat -> (length outputs <= 2019)%nat ->
  -signed_limit <= balance < signed_limit ->
  (jubjub_order | liability inputs - liability outputs - balance) ->
  liability inputs - liability outputs = balance.
Proof.
  intros inputs outputs balance HI HO HNI HNO HB HC.
  pose proof (bounded_note_sum _ HI) as SI.
  pose proof (bounded_note_sum _ HO) as SO.
  apply Nat2Z.inj_le in HNI; change (Z.of_nat (length inputs) <= 5208) in HNI.
  apply Nat2Z.inj_le in HNO; change (Z.of_nat (length outputs) <= 2019) in HNO.
  assert (DI : -jubjub_order < liability inputs - liability outputs - balance < jubjub_order).
  { unfold jubjub_order, note_limit, signed_limit in *; nia. }
  pose proof (bounded_multiple_is_zero _ DI HC); lia.
Qed.

Corollary native_binding_lifts_to_integer_balance : forall inputs outputs balance,
  bounded_notes inputs -> bounded_notes outputs ->
  (length inputs <= 5208)%nat -> (length outputs <= 2019)%nat ->
  -native_balance_limit <= balance <= native_balance_limit ->
  (jubjub_order | liability inputs - liability outputs - balance) ->
  liability inputs - liability outputs = balance.
Proof.
  intros. apply modular_binding_lifts_to_integer_balance; try assumption.
  unfold native_balance_limit, signed_limit in *; lia.
Qed.

(* Membership, uniqueness, freshness and witness-to-native-context
   correspondence remain separate cryptographic/context obligations. *)
Theorem extracted_modular_witness_gives_note_transition :
  forall before after consumed remaining created balance,
  Permutation before (consumed ++ remaining) ->
  after = remaining ++ created ->
  valid_notes before -> valid_notes after ->
  (forall n, In n created -> ~ In (note_id n) (map note_id before)) ->
  bounded_notes consumed -> bounded_notes created ->
  (length consumed <= 5208)%nat -> (length created <= 2019)%nat ->
  -native_balance_limit <= balance <= native_balance_limit ->
  (jubjub_order | liability consumed - liability created - balance) ->
  note_transition before after balance.
Proof.
  intros. eapply witnessed_note_transition; try eassumption.
  eapply native_binding_lifts_to_integer_balance; eassumption.
Qed.

Corollary extracted_modular_witness_gives_liability :
  forall before after consumed remaining created balance,
  Permutation before (consumed ++ remaining) ->
  after = remaining ++ created ->
  valid_notes before -> valid_notes after ->
  (forall n, In n created -> ~ In (note_id n) (map note_id before)) ->
  bounded_notes consumed -> bounded_notes created ->
  (length consumed <= 5208)%nat -> (length created <= 2019)%nat ->
  -native_balance_limit <= balance <= native_balance_limit ->
  (jubjub_order | liability consumed - liability created - balance) ->
  liability after = liability before - balance.
Proof.
  intros. apply note_transition_liability.
  eapply extracted_modular_witness_gives_note_transition; eassumption.
Qed.

(* This interface separates the remaining cryptographic/native extraction
   obligation from the arithmetic theorem above. Zero-valued dummy spends
   may be omitted from [consumed]; no membership of nonzero fake notes is
   allowed. The predicate assumes neither integer balance nor liability. *)
Inductive modular_note_witness (before after : list note) (balance : Z) : Prop :=
| modular_witness : forall consumed remaining created,
    Permutation before (consumed ++ remaining) ->
    after = remaining ++ created ->
    valid_notes before -> valid_notes after ->
    (forall n, In n created -> ~ In (note_id n) (map note_id before)) ->
    bounded_notes consumed -> bounded_notes created ->
    (length consumed <= 5208)%nat -> (length created <= 2019)%nat ->
    -native_balance_limit <= balance <= native_balance_limit ->
    (jubjub_order | liability consumed - liability created - balance) ->
    modular_note_witness before after balance.

Lemma modular_note_witness_transition : forall before after balance,
  modular_note_witness before after balance -> note_transition before after balance.
Proof.
  intros before after balance HW; destruct HW.
  eapply extracted_modular_witness_gives_note_transition; eassumption.
Qed.

Section AcceptedVerifier.
  Context {State Transaction Bound : Type}.
  Variable verify : Transaction -> State -> option (Bound * Z * State).
  Variable represents : State -> list note -> Prop.
  (* Idealized soundness on accepted executions. Instantiating this demands
     circuit/proof, signature, commitment, nullifier/context and FFI work.
     Computational failure probabilities are NOT formalized here. *)
  Hypothesis accepted_extracts_modular_witness : forall tx old bound balance next notes,
    verify tx old = Some (bound, balance, next) -> represents old notes ->
    exists next_notes, represents next next_notes /\
      modular_note_witness notes next_notes balance.

  Theorem accepted_verifier_integer_liability : forall tx old bound balance next notes,
    verify tx old = Some (bound, balance, next) -> represents old notes ->
    exists next_notes, represents next next_notes /\
      note_transition notes next_notes balance /\
      liability next_notes = liability notes - balance.
  Proof.
    intros tx old bound balance next notes HV HR.
    destruct (accepted_extracts_modular_witness _ _ _ _ _ _ HV HR) as [ns [HS HW]].
    pose proof (modular_note_witness_transition _ _ _ HW) as HT.
    exists ns; split; [exact HS|]. split; [exact HT|].
    now apply note_transition_liability.
  Qed.
End AcceptedVerifier.

(* Ordinary Z abs cannot wrap at signed-int64 minimum. Native balance
   validation rejects this value before Rust's checked_abs is reached. *)
Example mathematical_abs_signed_min : Z.abs (-signed_limit) = signed_limit.
Proof. reflexivity. Qed.
Example native_rejects_signed_min : ~ (-native_balance_limit <= -signed_limit <= native_balance_limit).
Proof. unfold native_balance_limit, signed_limit; lia. Qed.

(* Congruence alone is insufficient: a whole subgroup-order discrepancy
   satisfies it. This deliberately violates the source-derived bounds. *)
Example congruence_without_bounds_does_not_give_equality :
  (jubjub_order | jubjub_order) /\ jubjub_order <> 0.
Proof. split; [exists 1; ring|unfold jubjub_order; lia]. Qed.

Print Assumptions modular_binding_lifts_to_integer_balance.
Print Assumptions extracted_modular_witness_gives_liability.
Print Assumptions accepted_verifier_integer_liability.
