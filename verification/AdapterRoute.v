(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope string_scope.

(* Source-bound post-guard routing and immutable configuration.
   These theorems construct operations; they do not execute the called pool
   or issuer and do not establish the preceding sender/asset/tez guards. *)
Definition ingress_after_lookup (reject : list instruction) : list instruction :=
  [IfNone reject []; Push (VMutez 0); Dig 2; Prim "TRANSFER_TOKENS";
   Dip 1 [Dip 3 [Drop; Push (VBool true)]; PairN 4]; Nil; Swap; Cons; Pair].
Definition ingress_build (reject : list instruction) : list instruction :=
  [Dup 4; Nil; Swap; Cons; Swap; SomeValue; Pair; Dup 2; Prim "CONTRACT_pool"] ++
  ingress_after_lookup reject.
Definition egress_after_lookup (reject : list instruction) : list instruction :=
  [IfNone reject []; Push (VMutez 0); Dig 2; Prim "TRANSFER_TOKENS";
   Dip 1 [PairN 3]; Nil; Swap; Cons; Pair].
Definition egress_build (reject : list instruction) : list instruction :=
  [Dup 4; Swap; Nil; Swap; Cons; Swap; Pair; Nil; Swap; Cons; Dup 3; Car;
   Prim "CONTRACT_import"] ++ egress_after_lookup reject.

Section Route.
  Variable primitive : string -> stack -> option stack.
  Variable operation : value -> value -> value.
  Hypothesis transfer_frame : forall parameter handle rest,
    primitive "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) =
    Some (operation parameter handle :: rest).

  Lemma ingress_lookup_prefix : forall fuel reject ticket pool asset proof used frame,
    run primitive (9 + fuel)%nat (ingress_build reject)
      (ticket :: pool :: asset :: proof :: VBool used :: frame) =
    match primitive "CONTRACT_pool"
      (pool :: VPair (VSome ticket) (VList [proof]) :: pool :: asset :: proof :: VBool used :: frame) with
    | Some s => run primitive fuel (ingress_after_lookup reject) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma ingress_transfer_prefix : forall fuel reject ticket pool asset proof used handle frame,
    run primitive (4 + fuel)%nat (ingress_after_lookup reject)
      (VSome handle :: VPair (VSome ticket) (VList [proof]) :: pool :: asset :: proof :: VBool used :: frame) =
    match primitive "TRANSFER_TOKENS"
      (VPair (VSome ticket) (VList [proof]) :: VMutez 0 :: handle ::
       pool :: asset :: proof :: VBool used :: frame) with
    | Some s => run primitive fuel
        [Dip 1 [Dip 3 [Drop; Push (VBool true)]; PairN 4]; Nil; Swap; Cons; Pair] s
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma ingress_configuration_return : forall fuel op pool asset proof used frame,
    run primitive (6 + fuel)%nat
      [Dip 1 [Dip 3 [Drop; Push (VBool true)]; PairN 4]; Nil; Swap; Cons; Pair]
      (op :: pool :: asset :: proof :: VBool used :: frame) =
    Some (VPair (VList [op]) (VPair pool (VPair asset (VPair proof (VBool true)))) :: frame).
  Proof. reflexivity. Qed.

  Lemma egress_lookup_prefix : forall fuel reject ticket pool issuer contents beneficiary frame,
    run primitive (13 + fuel)%nat (egress_build reject)
      (ticket :: pool :: VPair issuer contents :: beneficiary :: frame) =
    match primitive "CONTRACT_import"
      (issuer :: VList [VPair beneficiary (VList [ticket])] ::
       pool :: VPair issuer contents :: beneficiary :: frame) with
    | Some s => run primitive fuel (egress_after_lookup reject) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma egress_transfer_prefix : forall fuel reject ticket pool issuer contents beneficiary handle frame,
    run primitive (4 + fuel)%nat (egress_after_lookup reject)
      (VSome handle :: VList [VPair beneficiary (VList [ticket])] ::
       pool :: VPair issuer contents :: beneficiary :: frame) =
    match primitive "TRANSFER_TOKENS"
      (VList [VPair beneficiary (VList [ticket])] :: VMutez 0 :: handle ::
       pool :: VPair issuer contents :: beneficiary :: frame) with
    | Some s => run primitive fuel [Dip 1 [PairN 3]; Nil; Swap; Cons; Pair] s
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma egress_configuration_return : forall fuel op pool asset beneficiary frame,
    run primitive (6 + fuel)%nat [Dip 1 [PairN 3]; Nil; Swap; Cons; Pair]
      (op :: pool :: asset :: beneficiary :: frame) =
    Some (VPair (VList [op]) (VPair pool (VPair asset beneficiary)) :: frame).
  Proof. reflexivity. Qed.

  Local Opaque run.

  Theorem ingress_uses_stored_pool_and_proof :
    forall reject ticket pool asset proof used handle frame,
    (forall rest, primitive "CONTRACT_pool" (pool :: rest) = Some (VSome handle :: rest)) ->
    run primitive 80 (ingress_build reject)
      (ticket :: pool :: asset :: proof :: VBool used :: frame) =
    Some (VPair
      (VList [operation (VPair (VSome ticket) (VList [proof])) handle])
      (VPair pool (VPair asset (VPair proof (VBool true)))) :: frame).
  Proof.
    intros reject ticket pool asset proof used handle frame H.
    rewrite (ingress_lookup_prefix 71), H, (ingress_transfer_prefix 67), transfer_frame.
    apply (ingress_configuration_return 61).
  Qed.

  Theorem egress_uses_stored_issuer_and_beneficiary :
    forall reject ticket pool issuer contents beneficiary handle frame,
    (forall rest, primitive "CONTRACT_import" (issuer :: rest) = Some (VSome handle :: rest)) ->
    run primitive 80 (egress_build reject)
      (ticket :: pool :: VPair issuer contents :: beneficiary :: frame) =
    Some (VPair
      (VList [operation (VList [VPair beneficiary (VList [ticket])]) handle])
      (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame).
  Proof.
    intros reject ticket pool issuer contents beneficiary handle frame H.
    rewrite (egress_lookup_prefix 67), H, (egress_transfer_prefix 63), transfer_frame.
    apply (egress_configuration_return 57).
  Qed.
End Route.

Print Assumptions ingress_uses_stored_pool_and_proof.
Print Assumptions egress_uses_stored_issuer_and_beneficiary.
