From Coq Require Import List String ZArith.
Require Import FullVM_WIP FA12LoopBody FA12MixedBatch.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* Structural loop converse. The per-step inverse is an explicit hypothesis
   here and must be discharged from the actual iteration before applying this
   theorem to a contract. It is not the desired contract conclusion. *)
Inductive step_event
  (verify : value -> value -> option (value * Z * value))
  (unpack : value -> option value) (pack : value -> list nat)
  (self sender handle : value) (operation : value -> value -> value) :
  value -> value -> list value -> list value -> value -> list value -> list value -> Prop :=
| event_positive : forall tx old ds ws bound balance next recipient,
    verify tx old = Some (bound,balance,next) -> 0 < balance ->
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    step_event verify unpack pack self sender handle operation tx old ds ws next ds
      (operation (VPair self (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws)
| event_negative : forall tx old ds ws balance next,
    verify tx old = Some (VBytes [],balance,next) -> balance < 0 ->
    step_event verify unpack pack self sender handle operation tx old ds ws next
      (operation (VPair sender (VPair self (VNat (Z.to_nat (Z.abs balance))))) handle :: ds) ws
| event_zero : forall tx old ds ws next,
    verify tx old = Some (VBytes [],0,next) ->
    step_event verify unpack pack self sender handle operation tx old ds ws next ds ws.

Section Extract.
  Variable prim : String.string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable self sender handle token : value.
  Variable operation : value -> value -> value.
  Variable frame : stack.
  Hypothesis step_inverse : forall tx old ds ws result,
    run prim 128 FA12LoopBody.iteration
      (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) = Some result ->
    exists next ds' ws',
      result = next :: handle :: token :: VPair (VList ds') (VList ws') :: frame /\
      step_event verify unpack pack self sender handle operation tx old ds ws next ds' ws'.

  Local Opaque run.

  Theorem successful_iteration_extracts_trace :
    forall txs old ds ws result,
    iterate (fun tx s => run prim 128 FA12LoopBody.iteration (tx :: s))
      txs (old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) = Some result ->
    exists final finalds finalws,
      result = final :: handle :: token :: VPair (VList finalds) (VList finalws) :: frame /\
      FA12MixedBatch.mixed_trace verify unpack pack self sender handle operation
        txs old ds ws final finalds finalws.
  Proof.
    induction txs as [|tx txs IH]; intros old ds ws result H.
    - cbn [iterate] in H. inversion H; subst.
      exists old, ds, ws. split; [reflexivity|constructor].
    - cbn [iterate] in H.
      destruct (run prim 128 FA12LoopBody.iteration
        (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame)) as [step|] eqn:HS;
        [|discriminate].
      destruct (step_inverse tx old ds ws step HS) as [next [ds' [ws' [E HE]]]].
      subst step.
      destruct (IH next ds' ws' result H) as [final [finalds [finalws [ER HT]]]].
      exists final, finalds, finalws. split; [exact ER|].
      inversion HE; subst.
      + eapply FA12MixedBatch.mixed_positive; eauto.
      + eapply FA12MixedBatch.mixed_negative; eauto.
      + eapply FA12MixedBatch.mixed_zero; eauto.
  Qed.
End Extract.
Print Assumptions successful_iteration_extracts_trace.
