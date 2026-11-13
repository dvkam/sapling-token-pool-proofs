(* SPDX-License-Identifier: MIT *)
From Coq Require Import List Arith.
Require Import InternalQueue.
Import ListNotations.

(* Source-shaped control flow of apply_manager_contents[_list]: the root
   contract has already changed its storage when its internal worklist runs.
   Storage-fee checks happen afterwards. A failure in ANY phase of ANY root
   rolls back to the manager-list snapshot, taken after upfront fee collection.
   This is a control-flow model, not a refinement of the OCaml implementation.
   Fuel counts internal dispatches, not gas. The nonce set is shared by roots. *)
Section ManagerBatch.
  Context {Context Root Internal : Type}.
  Variable nonce : Internal -> nat.
  Variable apply_internal : Context -> list nat -> Internal ->
    option (Context * list Internal).
  Variable apply_root : Context -> list nat -> Root ->
    option (Context * list Internal).
  Variable finish_root : Context -> option Context.

  Definition execute_root (fuel : nat) (ctxt : Context) (seen : list nat)
    (root : Root) : option (@completion Context Internal) :=
    match apply_root ctxt seen root with
    | None => None
    | Some (post_root, emitted) =>
      match run nonce apply_internal fuel post_root seen emitted with
      | None => None
      | Some q =>
        match finish_root (final_context q) with
        | None => None
        | Some finished => Some {| final_context := finished;
            final_seen := final_seen q; remaining_fuel := remaining_fuel q;
            executed := executed q |}
        end
      end
    end.

  Fixpoint run_batch (roots : list Root) (fuel : nat) (ctxt : Context)
    (seen : list nat) : option (@completion Context Internal) :=
    match roots with
    | [] => Some {| final_context := ctxt; final_seen := seen;
                   remaining_fuel := fuel; executed := [] |}
    | root :: rest =>
      match execute_root fuel ctxt seen root with
      | None => None
      | Some first => compose first
        (run_batch rest (remaining_fuel first) (final_context first)
          (final_seen first))
      end
    end.

  Theorem run_batch_append : forall prefix suffix fuel ctxt seen,
    run_batch (prefix ++ suffix) fuel ctxt seen =
    match run_batch prefix fuel ctxt seen with
    | None => None
    | Some first => compose first
        (run_batch suffix (remaining_fuel first) (final_context first)
          (final_seen first))
    end.
  Proof.
    induction prefix as [|root rest IH]; intros suffix fuel ctxt seen.
    - change (run_batch suffix fuel ctxt seen =
        compose {| final_context := ctxt; final_seen := seen;
                   remaining_fuel := fuel; executed := [] |}
          (run_batch suffix fuel ctxt seen)).
      destruct (run_batch suffix fuel ctxt seen) as [[c s f t]|]; reflexivity.
    - cbn [List.app run_batch].
      destruct (execute_root fuel ctxt seen root) as [first|]; [|reflexivity].
      rewrite IH.
      destruct (run_batch rest (remaining_fuel first) (final_context first)
        (final_seen first)) as [middle|];
        cbn [compose final_context final_seen remaining_fuel executed]; [|reflexivity].
      destruct (run_batch suffix (remaining_fuel middle) (final_context middle)
        (final_seen middle));
        cbn [compose final_context final_seen remaining_fuel executed];
        [rewrite app_assoc|]; reflexivity.
  Qed.

  Definition atomic_batch (roots : list Root) (fuel : nat) (ctxt : Context)
    (seen : list nat) : bool * Context :=
    match run_batch roots fuel ctxt seen with
    | None => (false, ctxt)
    | Some result => (true, final_context result)
    end.

  Theorem failed_batch_restores_pre_root_snapshot :
    forall roots fuel ctxt seen,
    fst (atomic_batch roots fuel ctxt seen) = false ->
    snd (atomic_batch roots fuel ctxt seen) = ctxt.
  Proof.
    intros. unfold atomic_batch in *.
    destruct (run_batch roots fuel ctxt seen); cbn in *;
      [discriminate|reflexivity].
  Qed.

  Theorem failed_suffix_rolls_back_prior_roots :
    forall prefix suffix fuel ctxt seen middle,
    run_batch prefix fuel ctxt seen = Some middle ->
    run_batch suffix (remaining_fuel middle) (final_context middle)
      (final_seen middle) = None ->
    atomic_batch (prefix ++ suffix) fuel ctxt seen = (false, ctxt).
  Proof.
    intros. unfold atomic_batch. rewrite run_batch_append, H, H0. reflexivity.
  Qed.

  Theorem late_fee_failure_rolls_back_root_and_descendants :
    forall root rest fuel ctxt seen post_root emitted q,
    apply_root ctxt seen root = Some (post_root, emitted) ->
    run nonce apply_internal fuel post_root seen emitted = Some q ->
    finish_root (final_context q) = None ->
    atomic_batch (root :: rest) fuel ctxt seen = (false, ctxt).
  Proof.
    intros. unfold atomic_batch. cbn [run_batch]. unfold execute_root.
    rewrite H, H0, H1. reflexivity.
  Qed.

  Variable invariant : Context -> list Internal -> Prop.
  Hypothesis root_preserves_pending : forall ctxt seen root next emitted,
    invariant ctxt [] -> apply_root ctxt seen root = Some (next, emitted) ->
    invariant next emitted.
  Hypothesis internal_preserves_pending : forall ctxt seen op rest next emitted,
    invariant ctxt (op :: rest) -> seen_nonce (nonce op) seen = false ->
    apply_internal ctxt (nonce op :: seen) op = Some (next, emitted) ->
    invariant next (emitted ++ rest).
  Hypothesis finish_preserves_settled : forall ctxt next,
    invariant ctxt [] -> finish_root ctxt = Some next -> invariant next [].

  Theorem successful_root_settles_pending : forall root fuel ctxt seen result,
    invariant ctxt [] -> execute_root fuel ctxt seen root = Some result ->
    invariant (final_context result) [].
  Proof.
    intros root fuel ctxt seen result I H. unfold execute_root in H.
    destruct (apply_root ctxt seen root) as [[next emitted]|] eqn:R;
      [|discriminate].
    destruct (run nonce apply_internal fuel next seen emitted) as [q|] eqn:Q;
      [|discriminate].
    destruct (finish_root (final_context q)) as [finished|] eqn:F;
      [|discriminate].
    inversion H; subst result. cbn. eapply finish_preserves_settled; [|exact F].
    eapply successful_queue_discharges_pending_invariant;
      [exact internal_preserves_pending| |exact Q].
    eapply root_preserves_pending; eauto.
  Qed.

  Theorem successful_batch_settles_every_root : forall roots fuel ctxt seen result,
    invariant ctxt [] -> run_batch roots fuel ctxt seen = Some result ->
    invariant (final_context result) [].
  Proof.
    induction roots as [|root rest IH]; intros fuel ctxt seen result I H;
      cbn [run_batch] in H.
    - inversion H; assumption.
    - destruct (execute_root fuel ctxt seen root) as [first|] eqn:R;
        [|discriminate].
      destruct (run_batch rest (remaining_fuel first) (final_context first)
        (final_seen first)) as [tail|] eqn:T; [|discriminate].
      cbn [compose] in H. inversion H; subst result. cbn.
      eapply IH; [|exact T]. eapply successful_root_settles_pending; eauto.
  Qed.

  Variable Projection : Type.
  Variable project : Context -> Projection.
  Variable collect_fees : Context -> option Context.
  Hypothesis fees_frame_asset : forall before paid,
    collect_fees before = Some paid -> project paid = project before.

  Theorem failed_after_fees_preserves_asset_projection :
    forall before paid roots fuel seen,
    collect_fees before = Some paid ->
    fst (atomic_batch roots fuel paid seen) = false ->
    project (snd (atomic_batch roots fuel paid seen)) = project before.
  Proof.
    intros before paid roots fuel seen F H.
    rewrite (failed_batch_restores_pre_root_snapshot _ _ _ _ H).
    now apply fees_frame_asset.
  Qed.
End ManagerBatch.

Print Assumptions run_batch_append.
Print Assumptions successful_batch_settles_every_root.
Print Assumptions failed_after_fees_preserves_asset_projection.
