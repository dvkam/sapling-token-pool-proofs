(* SPDX-License-Identifier: MIT *)
From Coq Require Import List Arith Lia.
Import ListNotations.

(* The worklist algorithm of Alpha apply_internal_operations: record a fresh
   nonce, apply one operation, then prepend its emitted operations to the
   remaining work. Fuel counts dispatcher steps, not protocol gas units.
   This formalizes the algorithm; a protocol context/step refinement is a
   separate obligation, not a hypothesis asserting contract safety. *)
Section Queue.
  Context {Context Operation : Type}.
  Variable nonce : Operation -> nat.
  Variable apply_one : Context -> list nat -> Operation ->
    option (Context * list Operation).

  Record completion := {
    final_context : Context;
    final_seen : list nat;
    remaining_fuel : nat;
    executed : list Operation
  }.

  Definition seen_nonce (n : nat) (seen : list nat) : bool :=
    existsb (Nat.eqb n) seen.

  Fixpoint run (fuel : nat) (ctxt : Context) (seen : list nat)
    (work : list Operation) : option completion :=
    match work with
    | [] => Some {| final_context := ctxt; final_seen := seen;
                    remaining_fuel := fuel; executed := [] |}
    | op :: rest =>
      match fuel with
      | 0 => None
      | S f =>
        if seen_nonce (nonce op) seen then None else
        match apply_one ctxt (nonce op :: seen) op with
        | None => None
        | Some (next, emitted) =>
          match run f next (nonce op :: seen) (emitted ++ rest) with
          | None => None
          | Some result => Some {| final_context := final_context result;
               final_seen := final_seen result;
               remaining_fuel := remaining_fuel result;
               executed := op :: executed result |}
          end
        end
      end
    end.

  Definition compose (prefix : completion)
    (suffix : option completion) : option completion :=
    match suffix with
    | None => None
    | Some result => Some {| final_context := final_context result;
         final_seen := final_seen result;
         remaining_fuel := remaining_fuel result;
         executed := executed prefix ++ executed result |}
    end.

  Theorem run_append : forall fuel ctxt seen prefix suffix,
    run fuel ctxt seen (prefix ++ suffix) =
    match run fuel ctxt seen prefix with
    | None => None
    | Some middle => compose middle
        (run (remaining_fuel middle) (final_context middle)
          (final_seen middle) suffix)
    end.
  Proof.
    induction fuel as [|fuel IH]; intros ctxt seen prefix suffix;
      destruct prefix as [|op rest].
    - cbn [run compose]. destruct suffix; reflexivity.
    - reflexivity.
    - change (run (S fuel) ctxt seen suffix =
        compose {| final_context := ctxt; final_seen := seen;
                   remaining_fuel := S fuel; executed := [] |}
          (run (S fuel) ctxt seen suffix)).
      destruct (run (S fuel) ctxt seen suffix) as [[c s f t]|]; reflexivity.
    - cbn [List.app run].
      destruct (seen_nonce (nonce op) seen); [reflexivity|].
      destruct (apply_one ctxt (nonce op :: seen) op) as [[next emitted]|]; [|reflexivity].
      rewrite app_assoc, IH.
      destruct (run fuel next (nonce op :: seen) (emitted ++ rest)) as [middle|];
        cbn [compose final_context final_seen remaining_fuel executed]; [|reflexivity].
      destruct (run (remaining_fuel middle) (final_context middle)
        (final_seen middle) suffix);
        cbn [compose final_context final_seen remaining_fuel executed]; reflexivity.
  Qed.

  Theorem successful_step_runs_descendants_before_siblings :
    forall fuel ctxt seen op siblings result,
    run (S fuel) ctxt seen (op :: siblings) = Some result ->
    seen_nonce (nonce op) seen = false /\
    exists next emitted descendants following,
      apply_one ctxt (nonce op :: seen) op = Some (next, emitted) /\
      run fuel next (nonce op :: seen) emitted = Some descendants /\
      run (remaining_fuel descendants) (final_context descendants)
        (final_seen descendants) siblings = Some following /\
      final_context result = final_context following /\
      final_seen result = final_seen following /\
      remaining_fuel result = remaining_fuel following /\
      executed result = op :: executed descendants ++ executed following.
  Proof.
    intros fuel ctxt seen op siblings result H.
    cbn [run] in H.
    destruct (seen_nonce (nonce op) seen) eqn:F; [discriminate|].
    split; [reflexivity|].
    destruct (apply_one ctxt (nonce op :: seen) op) as [[next emitted]|] eqn:S;
      [|discriminate].
    rewrite run_append in H.
    destruct (run fuel next (nonce op :: seen) emitted) as [descendants|] eqn:D;
      [|discriminate].
    destruct (run (remaining_fuel descendants) (final_context descendants)
      (final_seen descendants) siblings) as [following|] eqn:E;
      [|discriminate].
    cbn [compose] in H. inversion H; subst result.
    exists next, emitted, descendants, following. repeat split; auto.
  Qed.

  Theorem successful_run_counts_dispatcher_steps : forall fuel ctxt seen work result,
    run fuel ctxt seen work = Some result ->
    length (executed result) + remaining_fuel result = fuel.
  Proof.
    induction fuel as [|fuel IH]; intros ctxt seen work result H;
      destruct work as [|op rest]; cbn [run] in H.
    - inversion H; reflexivity.
    - discriminate.
    - inversion H; reflexivity.
    - destruct (seen_nonce (nonce op) seen); [discriminate|].
      destruct (apply_one ctxt (nonce op :: seen) op) as [[next emitted]|]; [|discriminate].
      destruct (run fuel next (nonce op :: seen) (emitted ++ rest)) as [tail|] eqn:T;
        [|discriminate].
      inversion H; subst result. cbn. specialize (IH _ _ _ _ T). lia.
  Qed.

  Lemma seen_nonce_true : forall n seen,
    seen_nonce n seen = true <-> In n seen.
  Proof.
    intros n seen. unfold seen_nonce. rewrite existsb_exists.
    split.
    - intros [x [HX E]]. apply Nat.eqb_eq in E. now subst.
    - intros H. exists n. split; [exact H|apply Nat.eqb_refl].
  Qed.

  Lemma seen_nonce_false : forall n seen,
    seen_nonce n seen = false <-> ~ In n seen.
  Proof.
    intros n seen. split.
    - intros E H. apply seen_nonce_true in H. rewrite E in H. discriminate.
    - intros H. destruct (seen_nonce n seen) eqn:E; [|reflexivity].
      exfalso. apply H. now apply seen_nonce_true.
  Qed.

  Theorem successful_queue_never_replays_a_nonce :
    forall fuel ctxt seen work result,
    NoDup seen -> run fuel ctxt seen work = Some result -> NoDup (final_seen result).
  Proof.
    induction fuel as [|fuel IH]; intros ctxt seen work result ND H;
      destruct work as [|op rest]; cbn [run] in H.
    - inversion H; assumption.
    - discriminate.
    - inversion H; assumption.
    - destruct (seen_nonce (nonce op) seen) eqn:F; [discriminate|].
      destruct (apply_one ctxt (nonce op :: seen) op) as [[next emitted]|]; [|discriminate].
      destruct (run fuel next (nonce op :: seen) (emitted ++ rest)) as [tail|] eqn:T;
        [|discriminate].
      inversion H; subst result. cbn. eapply IH; [|exact T].
      constructor; [now apply seen_nonce_false|exact ND].
  Qed.

  Theorem successful_queue_records_exactly_the_executed_nonces :
    forall fuel ctxt seen work result,
    run fuel ctxt seen work = Some result ->
    final_seen result = rev (map nonce (executed result)) ++ seen.
  Proof.
    induction fuel as [|fuel IH]; intros ctxt seen work result H;
      destruct work as [|op rest]; cbn [run] in H.
    - inversion H; reflexivity.
    - discriminate.
    - inversion H; reflexivity.
    - destruct (seen_nonce (nonce op) seen); [discriminate|].
      destruct (apply_one ctxt (nonce op :: seen) op) as [[next emitted]|]; [|discriminate].
      destruct (run fuel next (nonce op :: seen) (emitted ++ rest)) as [tail|] eqn:T;
        [|discriminate].
      inversion H; subst result. cbn.
      rewrite (IH _ _ _ _ T). rewrite <- app_assoc. reflexivity.
  Qed.

  Variable pending_invariant : Context -> list Operation -> Prop.
  Hypothesis step_preserves_pending_invariant :
    forall ctxt seen op rest next emitted,
    pending_invariant ctxt (op :: rest) ->
    seen_nonce (nonce op) seen = false ->
    apply_one ctxt (nonce op :: seen) op = Some (next, emitted) ->
    pending_invariant next (emitted ++ rest).

  Theorem successful_queue_discharges_pending_invariant :
    forall fuel ctxt seen work result,
    pending_invariant ctxt work -> run fuel ctxt seen work = Some result ->
    pending_invariant (final_context result) [].
  Proof.
    induction fuel as [|fuel IH]; intros ctxt seen work result I H;
      destruct work as [|op rest]; cbn [run] in H.
    - inversion H; assumption.
    - discriminate.
    - inversion H; assumption.
    - destruct (seen_nonce (nonce op) seen) eqn:F; [discriminate|].
      destruct (apply_one ctxt (nonce op :: seen) op) as [[next emitted]|] eqn:S;
        [|discriminate].
      destruct (run fuel next (nonce op :: seen) (emitted ++ rest)) as [tail|] eqn:T;
        [|discriminate].
      inversion H; subst result. cbn.
      eapply IH; [|exact T]. eapply step_preserves_pending_invariant; eauto.
  Qed.

  Definition atomic (fuel : nat) (ctxt : Context) (seen : list nat)
    (operations : list Operation) : bool * Context :=
    match run fuel ctxt seen operations with
    | None => (false, ctxt)
    | Some result => (true, final_context result)
    end.

  Theorem failed_queue_snapshot_preserves_asset_projection :
    forall (AssetProjection : Type) (project : Context -> AssetProjection)
      fuel ctxt seen operations,
    fst (atomic fuel ctxt seen operations) = false ->
    project (snd (atomic fuel ctxt seen operations)) = project ctxt.
  Proof.
    intros. unfold atomic in *. destruct (run fuel ctxt seen operations);
      cbn in *; [discriminate|reflexivity].
  Qed.

  Theorem committed_queue_snapshot_discharges_pending_invariant :
    forall fuel ctxt seen operations,
    pending_invariant ctxt operations ->
    fst (atomic fuel ctxt seen operations) = true ->
    pending_invariant (snd (atomic fuel ctxt seen operations)) [].
  Proof.
    intros fuel ctxt seen operations I H. unfold atomic in *.
    destruct (run fuel ctxt seen operations) as [result|] eqn:R;
      cbn in *; [|discriminate].
    eapply successful_queue_discharges_pending_invariant; eauto.
  Qed.
End Queue.

Print Assumptions successful_step_runs_descendants_before_siblings.
Print Assumptions successful_queue_discharges_pending_invariant.
Print Assumptions failed_queue_snapshot_preserves_asset_projection.
