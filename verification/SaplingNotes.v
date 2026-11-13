(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith Lia Sorting.Permutation.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope Z_scope.

(* A ghost view of live, spendable notes, not a public RPC enumeration.
   Zero-valued dummy notes are allowed. Identifiers model unique commitments;
   real commitments/nullifiers and their cryptographic relation are external. *)
Record note := Note { note_id : nat; note_value : nat }.
Fixpoint liability (notes : list note) : Z :=
  match notes with [] => 0 | n :: ns => Z.of_nat (note_value n) + liability ns end.
Definition valid_notes ns := NoDup (map note_id ns).
Lemma liability_app : forall a b, liability (a ++ b) = liability a + liability b.
Proof. induction a; intros; cbn [app liability]; [lia|rewrite IHa; lia]. Qed.
Lemma liability_nonnegative : forall ns, 0 <= liability ns.
Proof. induction ns; cbn [liability]; lia. Qed.
Lemma liability_permutation : forall a b, Permutation a b -> liability a = liability b.
Proof. intros a b H; induction H; cbn [liability]; try lia; congruence. Qed.

(* Witness law from transaction soundness: real consumed notes were live,
   outputs are fresh, and input value minus output value is the public balance.
   It mentions no ledger, reserve, collateral or contract safety predicate. *)
Inductive note_transition (before after : list note) (balance : Z) : Prop :=
| witnessed_note_transition : forall consumed remaining created,
    Permutation before (consumed ++ remaining) ->
    after = remaining ++ created ->
    valid_notes before -> valid_notes after ->
    (forall n, In n created -> ~ In (note_id n) (map note_id before)) ->
    liability consumed - liability created = balance ->
    note_transition before after balance.

Theorem note_transition_liability : forall before after balance,
  note_transition before after balance -> liability after = liability before - balance.
Proof.
  intros before after balance H; destruct H as [consumed remaining created HP HE HV HW HF HB].
  rewrite (liability_permutation _ _ HP), HE, !liability_app. lia.
Qed.
Theorem cannot_withdraw_more_than_live_liability : forall before after balance,
  note_transition before after balance -> balance <= liability before.
Proof. intros; pose proof (note_transition_liability _ _ _ H); pose proof (liability_nonnegative after); lia. Qed.

(* State must include the Sapling context/diff, not merely a lazy-state ID.
   A context-sensitive bridge must instantiate this relation when connecting
   the existing value-only execution model to actual Octez contexts. *)
Section VerificationSoundness.
  Context {SaplingState Transaction Bound : Type}.
  Variable verify : Transaction -> SaplingState -> option (Bound * Z * SaplingState).
  Variable represents : SaplingState -> list note -> Prop.
  Hypothesis cryptographic_note_soundness : forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists next_notes, represents next next_notes /\ note_transition notes next_notes balance.

  Theorem successful_verification_exposes_note_accounting :
    forall tx old bound balance next notes,
    verify tx old = Some (bound,balance,next) -> represents old notes ->
    exists next_notes, represents next next_notes /\
      liability next_notes = liability notes - balance /\ valid_notes next_notes.
  Proof.
    intros. destruct (cryptographic_note_soundness _ _ _ _ _ _ H H0) as [ns [HR HT]].
    exists ns. split; [exact HR|]. split; [now apply note_transition_liability|].
    inversion HT; assumption.
  Qed.
End VerificationSoundness.

(* Regression for the source sign: minting two notes from public funds has
   balance -2; spending one unit to public funds has balance +1. *)
Example shield_sign : liability [Note 1 2] = liability [] - (-2).
Proof. reflexivity. Qed.
Example unshield_sign : liability [Note 2 1] = liability [Note 1 2] - 1.
Proof. reflexivity. Qed.
Print Assumptions note_transition_liability.
Print Assumptions successful_verification_exposes_note_accounting.
