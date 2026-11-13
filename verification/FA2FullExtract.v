From Coq Require Import List String ZArith.
Require Import FullVM_WIP FA2Boundary FA2Combined FA2PrivateSuccess.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(* Exact whole-program prefix decomposition. No trace or output shape is
   assumed. The iteration inverse must establish those separately. *)
Section Extract.
  Variable prim : string -> stack -> option stack.
  Variable amount : nat.
  Hypothesis amount_frame : forall rest,
    prim "AMOUNT" rest = Some (VMutez amount :: rest).

  Lemma guard_nonzero : forall fuel tail n s,
    run prim (7 + fuel)%nat
      ([Push (VMutez 0); CompareInt; IsEq; If [] [Unit; Fail]] ++ tail)
      (VMutez (S n) :: s) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.
  Theorem successful_full_call_extracts_loop :
    forall public txs old token id frame output,
    run prim 139 (FA2PrivateSuccess.full_private_code public)
      (VPair (VList txs) (VPair old (VPair token id)) :: frame) = Some output ->
    amount = 0%nat /\ exists middle,
      iterate (fun tx st => run prim 128 FA2Combined.canonical_iteration (tx :: st))
        txs (old :: VMap [] :: VList [] :: token :: id :: frame) = Some middle /\
      run prim 128 (FA2Boundary.private_post public) middle = Some output.
  Proof.
    intros public txs old token id frame output H.
    unfold FA2PrivateSuccess.full_private_code in H.
    rewrite (FA2PrivateSuccess.guard_step prim 138), amount_frame in H.
    destruct amount as [|n].
    2: { rewrite (guard_nonzero 131) in H. discriminate. }
    split; [reflexivity|].
    rewrite (FA2PrivateSuccess.guard_pass prim 133),
      (FA2PrivateSuccess.init_step prim 129),
      (FA2PrivateSuccess.loop_step prim 127) in H.
    destruct (iterate (fun tx st => run prim 128 FA2Combined.canonical_iteration (tx :: st))
      txs (old :: VMap [] :: VList [] :: token :: id :: frame)) as [middle|] eqn:HI;
      [|discriminate].
    exists middle. auto.
  Qed.
End Extract.
Print Assumptions successful_full_call_extracts_loop.
