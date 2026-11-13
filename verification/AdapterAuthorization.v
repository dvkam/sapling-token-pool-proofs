(* SPDX-License-Identifier: MIT *)
From Coq Require Import List String Ascii ZArith.
Require Import FullVM_WIP AdapterRoute.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(* Typed entry shapes are explicit below. Quantity positivity, comparable
   identity typing, source translation and Octez correspondence remain external.
   Callback equations specify primitive behavior, never successful guard results. *)
Fixpoint utf8_ascii (s : string) : list nat :=
  match s with EmptyString => [] | String ch rest => nat_of_ascii ch :: utf8_ascii rest end.
Definition reject (label : string) : list instruction := [Push (VString (utf8_ascii label)); Fail].
Definition tez_test (label : string) : list instruction :=
  [Prim "AMOUNT"; Push (VMutez 0); CompareInt; IsEq; If [] (reject label)].
Definition identity_test (label : string) : list instruction :=
  [ReadTicket; Dup 1; Car; Dip 1 [Dup 1; Cdr; Car]; Pair; Dup 5;
   Prim "COMPARE_value"; IsEq; If [] (reject label); Drop].
Definition ingress_setup : list instruction :=
  [Unpair; Dip 1 [UnpairN 4]; Dup 5; If (reject "FA21_INGRESS_USED") []].
Definition ingress_sender_test : list instruction :=
  [Prim "SENDER"; Dup 4; Car; Prim "COMPARE_value"; IsEq;
   If [] (reject "FA21_INGRESS_WRONG_SENDER")].
Definition ingress_full : list instruction :=
  tez_test "FA21_INGRESS_NONZERO_TEZ" ++ ingress_setup ++ ingress_sender_test ++
  identity_test "FA21_INGRESS_WRONG_ASSET" ++
  AdapterRoute.ingress_build (reject "FA21_INGRESS_BAD_POOL").
Definition beneficiary_test : list instruction :=
  [Dup 4; Prim "PACK_address"; Size; Push (VNat 28); CompareInt; IsEq;
   If [] (reject "FA21_EGRESS_NON_DEFAULT_BENEFICIARY")].
Definition egress_sender_test : list instruction :=
  [Prim "SENDER"; Dup 3; Prim "COMPARE_value"; IsEq;
   If [] (reject "FA21_EGRESS_WRONG_SENDER")].
Definition egress_full : list instruction :=
  tez_test "FA21_EGRESS_NONZERO_TEZ" ++ [Unpair; Dip 1 [UnpairN 3]] ++
  beneficiary_test ++ egress_sender_test ++ identity_test "FA21_EGRESS_WRONG_ASSET" ++
  AdapterRoute.egress_build (reject "FA21_EGRESS_BAD_ISSUER").
Definition optional_handle (x : option value) := match x with Some h => VSome h | None => VNone end.
Definition nat_comparison (left right : nat) : Z :=
  match Nat.compare left right with Lt => -1 | Eq => 0 | Gt => 1 end.
Lemma nat_comparison_zero : forall left right, nat_comparison left right = 0 <-> left = right.
Proof.
  intros. unfold nat_comparison. destruct (Nat.compare left right) eqn:E.
  - apply Nat.compare_eq_iff in E. tauto.
  - apply Nat.compare_lt_iff in E. split; [discriminate|intro H; subst; exact (False_rect _ (Nat.lt_irrefl _ E))].
  - apply Nat.compare_gt_iff in E. split; [discriminate|intro H; subst; exact (False_rect _ (Nat.lt_irrefl _ E))].
Qed.

Section Authorization.
  Variable prim : string -> stack -> option stack.
  Variable attached : nat.
  Variable sender : value.
  Variable compare_value : value -> value -> Z.
  Variable pack_address : value -> list nat.
  Variable pool_lookup import_lookup : value -> option value.
  Variable operation : value -> value -> value.
  Hypothesis amount_frame : forall rest, prim "AMOUNT" rest = Some (VMutez attached :: rest).
  Hypothesis sender_frame : forall rest, prim "SENDER" rest = Some (sender :: rest).
  Hypothesis compare_frame : forall left right rest,
    prim "COMPARE_value" (left :: right :: rest) = Some (VInt (compare_value left right) :: rest).
  Hypothesis compare_zero : forall left right, compare_value left right = 0 <-> left = right.
  Hypothesis pack_frame : forall address rest,
    prim "PACK_address" (address :: rest) = Some (VBytes (pack_address address) :: rest).
  Hypothesis pool_frame : forall address rest,
    prim "CONTRACT_pool" (address :: rest) = Some (optional_handle (pool_lookup address) :: rest).
  Hypothesis import_frame : forall address rest,
    prim "CONTRACT_import" (address :: rest) = Some (optional_handle (import_lookup address) :: rest).
  Hypothesis transfer_frame : forall parameter handle rest,
    prim "TRANSFER_TOKENS" (parameter :: VMutez 0 :: handle :: rest) = Some (operation parameter handle :: rest).

  Lemma primitive_step : forall fuel name tail s,
    run prim (S fuel) (Prim name :: tail) s =
    match prim name s with Some next => run prim fuel tail next | None => None end.
  Proof. reflexivity. Qed.

  Lemma amount_prefix : forall fuel label tail s,
    run prim (S fuel) (tez_test label ++ tail) s =
    match prim "AMOUNT" s with
    | Some next => run prim fuel ([Push (VMutez 0); CompareInt; IsEq; If [] (reject label)] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma amount_guard : forall padding label tail s,
    run prim (8 + padding)%nat ([Push (VMutez 0); CompareInt; IsEq; If [] (reject label)] ++ tail)
      (VMutez attached :: s) =
    if Nat.eqb attached 0 then run prim (4 + padding)%nat tail s else None.
  Proof. intros; destruct attached; reflexivity. Qed.

  Lemma ingress_setup_exact : forall padding tail ticket pool asset proof used frame,
    run prim (8 + padding)%nat (ingress_setup ++ tail)
      (VPair ticket (VPair pool (VPair asset (VPair proof (VBool used)))) :: frame) =
    if used then None else run prim (4 + padding)%nat tail
      (ticket :: pool :: asset :: proof :: VBool used :: frame).
  Proof. intros; destruct used; reflexivity. Qed.

  Lemma ingress_sender_prefix : forall fuel tail ticket pool issuer contents proof used frame,
    run prim (3 + fuel)%nat
      ([Dup 4; Car; Prim "COMPARE_value"; IsEq; If [] (reject "FA21_INGRESS_WRONG_SENDER")] ++ tail)
      (sender :: ticket :: pool :: VPair issuer contents :: proof :: VBool used :: frame) =
    match prim "COMPARE_value"
      (issuer :: sender :: ticket :: pool :: VPair issuer contents :: proof :: VBool used :: frame) with
    | Some next => run prim fuel ([IsEq; If [] (reject "FA21_INGRESS_WRONG_SENDER")] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma ingress_sender_step : forall fuel tail s,
    run prim (S fuel) (ingress_sender_test ++ tail) s =
    match prim "SENDER" s with
    | Some next => run prim fuel
      ([Dup 4; Car; Prim "COMPARE_value"; IsEq; If [] (reject "FA21_INGRESS_WRONG_SENDER")] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma equality_guard : forall padding label tail result rest,
    run prim (5 + padding)%nat ([IsEq; If [] (reject label)] ++ tail) (VInt result :: rest) =
    if Z.eqb result 0 then run prim (3 + padding)%nat tail rest else None.
  Proof. intros; destruct result; reflexivity. Qed.

  Lemma identity_prefix : forall fuel label tail ticketer payload quantity pool issuer contents rest,
    run prim (8 + fuel)%nat (identity_test label ++ tail)
      (VTicket ticketer payload quantity :: pool :: VPair issuer contents :: rest) =
    match prim "COMPARE_value"
      (VPair issuer contents :: VPair ticketer payload ::
       VPair ticketer (VPair payload (VNat quantity)) ::
       VTicket ticketer payload quantity :: pool :: VPair issuer contents :: rest) with
    | Some next => run prim (S fuel) ([IsEq; If [] (reject label); Drop] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma identity_guard : forall padding label tail result info rest,
    run prim (6 + padding)%nat ([IsEq; If [] (reject label); Drop] ++ tail)
      (VInt result :: info :: rest) =
    if Z.eqb result 0 then run prim (3 + padding)%nat tail rest else None.
  Proof. intros; destruct result; reflexivity. Qed.

  Lemma egress_setup_exact : forall fuel tail ticket pool asset beneficiary frame,
    run prim (4 + fuel)%nat ([Unpair; Dip 1 [UnpairN 3]] ++ tail)
      (VPair ticket (VPair pool (VPair asset beneficiary)) :: frame) =
    run prim (2 + fuel)%nat tail (ticket :: pool :: asset :: beneficiary :: frame).
  Proof. reflexivity. Qed.

  Lemma beneficiary_prefix : forall fuel tail ticket pool asset beneficiary frame,
    run prim (2 + fuel)%nat (beneficiary_test ++ tail)
      (ticket :: pool :: asset :: beneficiary :: frame) =
    match prim "PACK_address" (beneficiary :: ticket :: pool :: asset :: beneficiary :: frame) with
    | Some next => run prim fuel
      ([Size; Push (VNat 28); CompareInt; IsEq; If [] (reject "FA21_EGRESS_NON_DEFAULT_BENEFICIARY")] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma beneficiary_size_prefix : forall fuel bytes tail rest,
    run prim (3 + fuel)%nat
      ([Size; Push (VNat 28); CompareInt; IsEq; If [] (reject "FA21_EGRESS_NON_DEFAULT_BENEFICIARY")] ++ tail)
      (VBytes bytes :: rest) =
    run prim fuel ([IsEq; If [] (reject "FA21_EGRESS_NON_DEFAULT_BENEFICIARY")] ++ tail)
      (VInt (nat_comparison 28 (List.length bytes)) :: rest).
  Proof. reflexivity. Qed.

  Lemma beneficiary_guard : forall padding bytes tail rest,
    run prim (8 + padding)%nat
      ([Size; Push (VNat 28); CompareInt; IsEq; If [] (reject "FA21_EGRESS_NON_DEFAULT_BENEFICIARY")] ++ tail)
      (VBytes bytes :: rest) =
    if Z.eqb (nat_comparison 28 (List.length bytes)) 0
    then run prim (3 + padding)%nat tail rest else None.
  Proof. intros; rewrite (beneficiary_size_prefix (5 + padding)%nat). apply equality_guard. Qed.

  Lemma egress_sender_prefix : forall fuel tail ticket pool asset beneficiary frame,
    run prim (2 + fuel)%nat
      ([Dup 3; Prim "COMPARE_value"; IsEq; If [] (reject "FA21_EGRESS_WRONG_SENDER")] ++ tail)
      (sender :: ticket :: pool :: asset :: beneficiary :: frame) =
    match prim "COMPARE_value" (pool :: sender :: ticket :: pool :: asset :: beneficiary :: frame) with
    | Some next => run prim fuel ([IsEq; If [] (reject "FA21_EGRESS_WRONG_SENDER")] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma egress_sender_step : forall fuel tail s,
    run prim (S fuel) (egress_sender_test ++ tail) s =
    match prim "SENDER" s with
    | Some next => run prim fuel
      ([Dup 3; Prim "COMPARE_value"; IsEq; If [] (reject "FA21_EGRESS_WRONG_SENDER")] ++ tail) next
    | None => None end.
  Proof. reflexivity. Qed.

  Lemma ingress_missing_handle : forall ticket pool asset proof used frame,
    run prim 126 (AdapterRoute.ingress_after_lookup (reject "FA21_INGRESS_BAD_POOL"))
      (VNone :: VPair (VSome ticket) (VList [proof]) :: pool :: asset :: proof :: VBool used :: frame) = None.
  Proof. reflexivity. Qed.
  Lemma egress_missing_handle : forall ticket pool issuer contents beneficiary frame,
    run prim 118 (AdapterRoute.egress_after_lookup (reject "FA21_EGRESS_BAD_ISSUER"))
      (VNone :: VList [VPair beneficiary (VList [ticket])] :: pool :: VPair issuer contents :: beneficiary :: frame) = None.
  Proof. reflexivity. Qed.

  Local Opaque run.

  Lemma ingress_route_exact : forall ticket pool asset proof used frame,
    run prim 135 (AdapterRoute.ingress_build (reject "FA21_INGRESS_BAD_POOL"))
      (ticket :: pool :: asset :: proof :: VBool used :: frame) =
    match pool_lookup pool with
    | None => None
    | Some handle => Some (VPair
      (VList [operation (VPair (VSome ticket) (VList [proof])) handle])
      (VPair pool (VPair asset (VPair proof (VBool true)))) :: frame)
    end.
  Proof.
    intros. rewrite (AdapterRoute.ingress_lookup_prefix prim 126), pool_frame.
    destruct (pool_lookup pool); cbn [optional_handle].
    - rewrite (AdapterRoute.ingress_transfer_prefix prim 122), transfer_frame.
      apply (AdapterRoute.ingress_configuration_return prim 116).
    - apply ingress_missing_handle.
  Qed.

  Lemma egress_route_exact : forall ticket pool issuer contents beneficiary frame,
    run prim 131 (AdapterRoute.egress_build (reject "FA21_EGRESS_BAD_ISSUER"))
      (ticket :: pool :: VPair issuer contents :: beneficiary :: frame) =
    match import_lookup issuer with
    | None => None
    | Some handle => Some (VPair
      (VList [operation (VList [VPair beneficiary (VList [ticket])]) handle])
      (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame)
    end.
  Proof.
    intros. rewrite (AdapterRoute.egress_lookup_prefix prim 118), import_frame.
    destruct (import_lookup issuer); cbn [optional_handle].
    - rewrite (AdapterRoute.egress_transfer_prefix prim 114), transfer_frame.
      apply (AdapterRoute.egress_configuration_return prim 108).
    - apply egress_missing_handle.
  Qed.

  Theorem ingress_full_exact : forall ticketer payload quantity pool issuer contents proof used frame,
    run prim 160 ingress_full
      (VPair (VTicket ticketer payload quantity)
        (VPair pool (VPair (VPair issuer contents) (VPair proof (VBool used)))) :: frame) =
    if Nat.eqb attached 0 then
      if used then None else
      if Z.eqb (compare_value issuer sender) 0 then
      if Z.eqb (compare_value (VPair issuer contents) (VPair ticketer payload)) 0 then
      match pool_lookup pool with
      | Some handle => Some (VPair
          (VList [operation (VPair (VSome (VTicket ticketer payload quantity)) (VList [proof])) handle])
          (VPair pool (VPair (VPair issuer contents) (VPair proof (VBool true)))) :: frame)
      | None => None end else None else None
    else None.
  Proof.
    intros. unfold ingress_full.
    rewrite (amount_prefix 159), amount_frame, (amount_guard 151).
    destruct (Nat.eqb attached 0); [|reflexivity].
    rewrite (ingress_setup_exact 147). destruct used; [reflexivity|].
    rewrite (ingress_sender_step 150), sender_frame, (ingress_sender_prefix 147), compare_frame,
      (equality_guard 142).
    destruct (Z.eqb (compare_value issuer sender) 0); [|reflexivity].
    rewrite (identity_prefix 137), compare_frame, (identity_guard 132).
    destruct (Z.eqb (compare_value (VPair issuer contents) (VPair ticketer payload)) 0); [|reflexivity].
    apply ingress_route_exact.
  Qed.

  Theorem egress_full_exact : forall ticketer payload quantity pool issuer contents beneficiary frame,
    run prim 160 egress_full
      (VPair (VTicket ticketer payload quantity) (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame) =
    if Nat.eqb attached 0 then
    if Z.eqb (nat_comparison 28 (List.length (pack_address beneficiary))) 0 then
    if Z.eqb (compare_value pool sender) 0 then
    if Z.eqb (compare_value (VPair issuer contents) (VPair ticketer payload)) 0 then
      match import_lookup issuer with
      | Some handle => Some (VPair
          (VList [operation (VList [VPair beneficiary (VList [VTicket ticketer payload quantity])]) handle])
          (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame)
      | None => None end else None else None else None else None.
  Proof.
    intros. unfold egress_full.
    rewrite (amount_prefix 159), amount_frame, (amount_guard 151).
    destruct (Nat.eqb attached 0); [|reflexivity].
    rewrite (egress_setup_exact 151), (beneficiary_prefix 151), pack_frame, (beneficiary_guard 143).
    destruct (Z.eqb (nat_comparison 28 (List.length (pack_address beneficiary))) 0); [|reflexivity].
    rewrite (egress_sender_step 145), sender_frame, (egress_sender_prefix 143), compare_frame,
      (equality_guard 138).
    destruct (Z.eqb (compare_value pool sender) 0); [|reflexivity].
    rewrite (identity_prefix 133), compare_frame, (identity_guard 128).
    destruct (Z.eqb (compare_value (VPair issuer contents) (VPair ticketer payload)) 0); [|reflexivity].
    apply egress_route_exact.
  Qed.

  Theorem successful_ingress_requires_authorization_and_stored_route :
    forall ticketer payload quantity pool issuer contents proof used frame output,
    run prim 160 ingress_full
      (VPair (VTicket ticketer payload quantity)
        (VPair pool (VPair (VPair issuer contents) (VPair proof (VBool used)))) :: frame) = Some output ->
    attached = 0%nat /\ used = false /\ sender = issuer /\
    issuer = ticketer /\ contents = payload /\
    exists handle, pool_lookup pool = Some handle /\
      output = VPair
        (VList [operation (VPair (VSome (VTicket ticketer payload quantity)) (VList [proof])) handle])
        (VPair pool (VPair (VPair issuer contents) (VPair proof (VBool true)))) :: frame.
  Proof.
    intros ticketer payload quantity pool issuer contents proof used frame output H.
    rewrite ingress_full_exact in H.
    destruct (Nat.eqb attached 0) eqn:HA; [|discriminate].
    destruct used; [discriminate|].
    destruct (Z.eqb (compare_value issuer sender) 0) eqn:HS; [|discriminate].
    destruct (Z.eqb (compare_value (VPair issuer contents) (VPair ticketer payload)) 0) eqn:HI;
      [|discriminate].
    destruct (pool_lookup pool) as [handle|] eqn:HC; [|discriminate].
    apply Nat.eqb_eq in HA.
    apply Z.eqb_eq in HS. apply compare_zero in HS.
    apply Z.eqb_eq in HI. apply compare_zero in HI. injection HI as Hissuer Hcontents.
    split; [exact HA|]. split; [reflexivity|]. split; [symmetry; exact HS|].
    split; [exact Hissuer|]. split; [exact Hcontents|].
    exists handle. split; [reflexivity|]. inversion H; reflexivity.
  Qed.

  Theorem successful_egress_requires_authorization_and_stored_route :
    forall ticketer payload quantity pool issuer contents beneficiary frame output,
    run prim 160 egress_full
      (VPair (VTicket ticketer payload quantity) (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame) = Some output ->
    attached = 0%nat /\ List.length (pack_address beneficiary) = 28%nat /\
    sender = pool /\ issuer = ticketer /\ contents = payload /\
    exists handle, import_lookup issuer = Some handle /\
      output = VPair
        (VList [operation (VList [VPair beneficiary (VList [VTicket ticketer payload quantity])]) handle])
        (VPair pool (VPair (VPair issuer contents) beneficiary)) :: frame.
  Proof.
    intros ticketer payload quantity pool issuer contents beneficiary frame output H.
    rewrite egress_full_exact in H.
    destruct (Nat.eqb attached 0) eqn:HA; [|discriminate].
    destruct (Z.eqb (nat_comparison 28 (List.length (pack_address beneficiary))) 0) eqn:HB;
      [|discriminate].
    destruct (Z.eqb (compare_value pool sender) 0) eqn:HS; [|discriminate].
    destruct (Z.eqb (compare_value (VPair issuer contents) (VPair ticketer payload)) 0) eqn:HI;
      [|discriminate].
    destruct (import_lookup issuer) as [handle|] eqn:HC; [|discriminate].
    apply Nat.eqb_eq in HA.
    apply Z.eqb_eq in HB. apply nat_comparison_zero in HB.
    apply Z.eqb_eq in HS. apply compare_zero in HS.
    apply Z.eqb_eq in HI. apply compare_zero in HI. injection HI as Hissuer Hcontents.
    split; [exact HA|]. split; [symmetry; exact HB|]. split; [symmetry; exact HS|].
    split; [exact Hissuer|]. split; [exact Hcontents|].
    exists handle. split; [reflexivity|]. inversion H; reflexivity.
  Qed.
End Authorization.

Print Assumptions ingress_full_exact.
Print Assumptions egress_full_exact.
Print Assumptions successful_ingress_requires_authorization_and_stored_route.
Print Assumptions successful_egress_requires_authorization_and_stored_route.
