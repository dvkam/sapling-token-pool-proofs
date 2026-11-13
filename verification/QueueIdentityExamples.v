(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith Lia.
Require Import FullVM_WIP AssetLedger InternalQueue CollateralCallTree.
Import ListNotations.
Open Scope Z_scope.

(* The full native identity is distinct from the deterministic erased call.
   The actual nonce allocator and its bound require protocol refinement. *)
Record native_operation := NativeOperation { identity : nat; erased_call : value }.
Section Regressions.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Definition payer := VNat 1.
  Definition pool := VNat 2.
  Definition handle := VOpaque 44.
  Definition deposit := Transfer payer pool 1.
  Definition repeated_payload := VPair handle (fa12_parameter deposit).
  Definition decode_wire (v : value) : option transfer :=
    match v with VPair target parameter =>
      if eq_value target handle then decode_fa12_parameter parameter else None
    | _ => None end.
  Definition projected (v : value) : list transfer :=
    match decode_wire v with Some t => [t] | None => [] end.
  Definition initial : ledger := fun account => if eq_value account payer then 2 else 0.
  Definition after_one := move eq_value initial deposit.
  Definition after_two := move eq_value after_one deposit.
  Definition apply_issuer (l : ledger) (_seen : list nat) (op : native_operation)
    : option (ledger * list native_operation) :=
    match decode_wire (erased_call op) with
    | None => None
    | Some t => if Z.geb (l (from_account t)) (Z.of_nat (units t))
      then Some (move eq_value l t, []) else None end.

  Lemma payload_decodes_exact_deposit : decode_wire repeated_payload = Some deposit.
  Proof.
    unfold repeated_payload, decode_wire. destruct (eq_value handle handle); [|contradiction].
    apply decode_fa12_exact.
  Qed.
  Lemma initial_payer : initial payer = 2.
  Proof. unfold initial; destruct (eq_value payer payer); [reflexivity|contradiction]. Qed.
  Lemma initial_pool : initial pool = 0.
  Proof. unfold initial; destruct (eq_value pool payer); [discriminate|reflexivity]. Qed.
  Lemma payer_after_first_real_debit : after_one payer = 1.
  Proof.
    unfold after_one,deposit. rewrite move_reserve_effect, initial_payer.
    unfold reserve_delta. cbn [from_account to_account units].
    destruct (eq_value payer pool); [discriminate|].
    destruct (eq_value payer payer); [reflexivity|contradiction].
  Qed.
  Lemma first_reserve_effect : after_one pool = 1.
  Proof.
    unfold after_one,deposit. rewrite move_reserve_effect,initial_pool.
    rewrite deposit_delta by discriminate. reflexivity.
  Qed.
  Lemma second_reserve_effect : after_two pool = 2.
  Proof.
    unfold after_two,deposit. rewrite move_reserve_effect,first_reserve_effect.
    rewrite deposit_delta by discriminate. reflexivity.
  Qed.
  Lemma funded_first_step : forall seen,
    apply_issuer initial seen (NativeOperation 1 repeated_payload) = Some (after_one,[]).
  Proof.
    intros. unfold apply_issuer. cbn [erased_call]. rewrite payload_decodes_exact_deposit.
    cbn [deposit from_account units]. rewrite initial_payer. reflexivity.
  Qed.
  Lemma funded_second_step : forall seen,
    apply_issuer after_one seen (NativeOperation 2 repeated_payload) = Some (after_two,[]).
  Proof.
    intros. unfold apply_issuer. cbn [erased_call]. rewrite payload_decodes_exact_deposit.
    cbn [deposit from_account units]. rewrite payer_after_first_real_debit. reflexivity.
  Qed.

  Theorem equal_payloads_distinct_nonces_execute_two_real_effects :
    exists result,
      InternalQueue.run identity apply_issuer 2 initial []
        [NativeOperation 1 repeated_payload; NativeOperation 2 repeated_payload] = Some result /\
      final_seen result = [2;1]%nat /\
      executed result = [NativeOperation 1 repeated_payload; NativeOperation 2 repeated_payload] /\
      final_context result pool = 2.
  Proof.
    exists {| final_context := after_two; final_seen := [2;1]%nat;
      remaining_fuel := 0%nat;
      executed := [NativeOperation 1 repeated_payload; NativeOperation 2 repeated_payload] |}.
    split.
    - cbn [InternalQueue.run seen_nonce identity existsb Nat.eqb].
      rewrite funded_first_step. cbn [List.app InternalQueue.run seen_nonce identity existsb Nat.eqb].
      rewrite funded_second_step. reflexivity.
    - repeat split; try reflexivity. exact second_reserve_effect.
  Qed.

  Theorem payload_erasure_preserves_order_and_multiplicity :
    map erased_call [NativeOperation 1 repeated_payload; NativeOperation 2 repeated_payload] =
      [repeated_payload;repeated_payload] /\
    pending_movements erased_call projected
      [NativeOperation 1 repeated_payload; NativeOperation 2 repeated_payload] = [deposit;deposit] /\
    net_delta eq_value pool [deposit;deposit] = 2.
  Proof.
    split; [reflexivity|]. split.
    - assert (HP : projected repeated_payload = [deposit]).
      { unfold projected. rewrite payload_decodes_exact_deposit. reflexivity. }
      cbn [pending_movements erased_call]. rewrite HP. reflexivity.
    - cbn [net_delta]. unfold deposit. rewrite deposit_delta by discriminate. reflexivity.
  Qed.

  (* No premise concerning the second payload/decoder/issuer step is used:
     nonce replay rejects before that step, even with a different payload. *)
  Theorem reused_nonce_rejects_any_second_payload : forall second_payload,
    InternalQueue.run identity apply_issuer 2 initial []
      [NativeOperation 1 repeated_payload; NativeOperation 1 second_payload] = None.
  Proof.
    intros. cbn [InternalQueue.run seen_nonce identity existsb Nat.eqb].
    rewrite funded_first_step. reflexivity.
  Qed.
  Theorem reused_nonce_rolls_back_first_deposit : forall second_payload,
    atomic identity apply_issuer 2 initial []
      [NativeOperation 1 repeated_payload; NativeOperation 1 second_payload] = (false,initial).
  Proof. intros. unfold atomic. rewrite reused_nonce_rejects_any_second_payload. reflexivity. Qed.
End Regressions.
Print Assumptions equal_payloads_distinct_nonces_execute_two_real_effects.
Print Assumptions payload_erasure_preserves_order_and_multiplicity.
Print Assumptions reused_nonce_rolls_back_first_deposit.
