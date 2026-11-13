From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* Actual FA1.2 transaction-body programs in the shared partial VM.
   TRANSFER_TOKENS constructs a deferred operation; it does not execute the
   token or change its ledger here. Callback/Octez correspondence, gas, typed
   linearity, Sapling cryptography, external execution and rollback are open.
   Frame equations below are explicit local premises, not global axioms. *)
Section FA12Body.
  Variable primitive : string -> stack -> option stack.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable self sender : value.
  Variable make_operation : value -> value -> value.
  Hypothesis verify_some_frame : forall tx old bound balance next rest,
    verify tx old = Some (bound, balance, next) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some (VSome (VPair bound (VPair (VInt balance) next)) :: rest).
  Hypothesis verify_none_frame : forall tx old rest,
    verify tx old = None ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) = Some (VNone :: rest).
  Hypothesis unpack_some_frame : forall bound recipient rest,
    unpack bound = Some recipient ->
    primitive "UNPACK_address" (bound :: rest) = Some (VSome recipient :: rest).
  Hypothesis unpack_none_frame : forall bound rest,
    unpack bound = None -> primitive "UNPACK_address" (bound :: rest) = Some (VNone :: rest).
  Hypothesis pack_frame : forall recipient rest,
    primitive "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).
  Hypothesis self_frame : forall rest, primitive "SELF_ADDRESS" rest = Some (self :: rest).
  Hypothesis sender_frame : forall rest, primitive "SENDER" rest = Some (sender :: rest).
  Hypothesis operation_frame : forall parameters handle rest,
    primitive "TRANSFER_TOKENS" (parameters :: VMutez 0 :: handle :: rest) =
    Some (make_operation parameters handle :: rest).

  Definition fail : list instruction := [Unit; Fail].
  Definition recipient_failure : list instruction :=
    [Push (VString ([70;65;95;78;79;78;95;68;69;70;65;85;76;84;95;82;69;67;73;80;73;69;78;84]%nat)); Fail].
  Definition address_if : list instruction := [If [] recipient_failure].
  Definition address_packed : list instruction := [Size; Push (VNat 28); CompareInt; IsEq] ++ address_if.
  Definition address_unpacked : list instruction := [IfNone fail []; Dup 1; Prim "PACK_address"] ++ address_packed.
  Definition address_guard : list instruction := Prim "UNPACK_address" :: address_unpacked.
  Definition empty_guard : list instruction := [Size; Push (VNat 0); CompareInt; IsEq; If [] fail].

  Definition append_out : list instruction := [Swap; Unpair; Dip 1 [Swap; Cons]; Pair].
  Definition append_in : list instruction := [Swap; Unpair; Dig 2; Cons; Pair].
  Definition after_out : list instruction := [Dug 2; Dip 2 append_out].
  Definition after_in : list instruction := [Dug 2; Dip 2 append_in].
  Definition transfer_prefix (tail : list instruction) : list instruction :=
    [PairN 3; Swap; Dup 1; Push (VMutez 0); Dig 3; Prim "TRANSFER_TOKENS"] ++ tail.
  Definition build_out : list instruction := [Swap; Prim "SELF_ADDRESS"] ++ transfer_prefix after_out.
  Definition build_in_after_self : list instruction := Prim "SENDER" :: transfer_prefix after_in.
  Definition build_in : list instruction := Prim "SELF_ADDRESS" :: build_in_after_self.
  Definition positive_after_guard : list instruction := [Swap; Dip 1 build_out].
  Definition positive_branch : list instruction := [Drop; Dip 2 address_guard] ++ positive_after_guard.
  Definition incoming_case : list instruction := [Swap; Dip 1 build_in].
  Definition after_empty_guard : list instruction := [IsLt; If incoming_case [Drop]].
  Definition nonpositive_branch : list instruction := Dip 3 empty_guard :: after_empty_guard.
  Definition iteration : list instruction :=
    [Prim "SAPLING_VERIFY_UPDATE"; IfNone fail []; UnpairN 3;
     Dug 2; Dup 1; Dup 1; Abs; Dug 2; IsGt; If positive_branch nonpositive_branch].

  (* Small symbolic-fuel blocks keep unknown callback continuations opaque. *)
  Lemma address_unpack_step : forall fuel bound rest,
    run primitive (S fuel) address_guard (bound :: rest) =
    match primitive "UNPACK_address" (bound :: rest) with
    | Some s => run primitive fuel address_unpacked s | None => None end.
  Proof. reflexivity. Qed.
  Lemma address_pack_step : forall fuel recipient rest,
    run primitive (3 + fuel)%nat address_unpacked (VSome recipient :: rest) =
    match primitive "PACK_address" (recipient :: recipient :: rest) with
    | Some s => run primitive fuel address_packed s | None => None end.
  Proof. reflexivity. Qed.
  Lemma address_compare_step : forall fuel bytes recipient rest,
    run primitive (4 + fuel)%nat address_packed (VBytes bytes :: recipient :: rest) =
    run primitive fuel address_if
      (VBool (Z.eqb (match Nat.compare 28 (List.length bytes) with Lt => -1 | Eq => 0 | Gt => 1 end) 0) :: recipient :: rest).
  Proof. reflexivity. Qed.
  Lemma address_if_good : forall fuel recipient rest,
    run primitive (2 + fuel)%nat address_if (VBool true :: recipient :: rest) = Some (recipient :: rest).
  Proof. reflexivity. Qed.
  Lemma address_if_bad : forall fuel recipient rest,
    run primitive (4 + fuel)%nat address_if (VBool false :: recipient :: rest) = None.
  Proof. reflexivity. Qed.
  Lemma address_none_bad : forall fuel rest,
    run primitive (4 + fuel)%nat address_unpacked (VNone :: rest) = None.
  Proof. reflexivity. Qed.

  Lemma out_self_step : forall fuel amount recipient handle token ds ws frame,
    run primitive (2 + fuel)%nat build_out
      (VNat amount :: recipient :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match primitive "SELF_ADDRESS"
      (recipient :: VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => run primitive fuel (transfer_prefix after_out) s | None => None end.
  Proof. reflexivity. Qed.
  Lemma transfer_step : forall fuel tail from_ to_ amount handle token ds ws frame,
    run primitive (6 + fuel)%nat (transfer_prefix tail)
      (from_ :: to_ :: VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match primitive "TRANSFER_TOKENS"
      (VPair from_ (VPair to_ (VNat amount)) :: VMutez 0 :: handle :: handle :: token ::
       VPair (VList ds) (VList ws) :: frame) with
    | Some s => run primitive fuel tail s | None => None end.
  Proof. reflexivity. Qed.
  Lemma append_out_step : forall fuel op handle token ds ws frame,
    run primitive (10 + fuel)%nat after_out
      (op :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (handle :: token :: VPair (VList ds) (VList (op :: ws)) :: frame).
  Proof. reflexivity. Qed.
  Lemma append_in_step : forall fuel op handle token ds ws frame,
    run primitive (10 + fuel)%nat after_in
      (op :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (handle :: token :: VPair (VList (op :: ds)) (VList ws) :: frame).
  Proof. reflexivity. Qed.
  Lemma in_self_step : forall fuel amount handle token ds ws frame,
    run primitive (S fuel) build_in
      (VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match primitive "SELF_ADDRESS"
      (VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => run primitive fuel build_in_after_self s | None => None end.
  Proof. reflexivity. Qed.
  Lemma in_sender_step : forall fuel amount handle token ds ws frame,
    run primitive (S fuel) build_in_after_self
      (self :: VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match primitive "SENDER"
      (self :: VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => run primitive fuel (transfer_prefix after_in) s | None => None end.
  Proof. reflexivity. Qed.

  Lemma positive_guard_step : forall fuel balance amount state bound handle token ds ws frame,
    run primitive (2 + fuel)%nat positive_branch
      (VInt balance :: VNat amount :: state :: bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match run primitive fuel address_guard (bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => run primitive fuel positive_after_guard (VNat amount :: state :: s) | None => None end.
  Proof.
    intros. cbn [positive_branch run Nat.add List.app List.length firstn skipn Nat.leb].
    destruct (run primitive fuel address_guard
      (bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame)); reflexivity.
  Qed.
  Lemma positive_build_step : forall fuel amount state recipient handle token ds ws frame,
    run primitive (2 + S fuel)%nat positive_after_guard
      (VNat amount :: state :: recipient :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match (match run primitive (S fuel) build_out
      (VNat amount :: recipient :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => Some (state :: s) | None => None end) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Lemma empty_guard_good : forall fuel rest,
    run primitive (7 + fuel)%nat empty_guard (VBytes [] :: rest) = Some rest.
  Proof. reflexivity. Qed.
  Lemma empty_guard_bad : forall fuel byte bytes rest,
    run primitive (7 + fuel)%nat empty_guard (VBytes (byte :: bytes) :: rest) = None.
  Proof. reflexivity. Qed.
  Lemma nonpositive_guard_step : forall fuel balance amount state bound handle token ds ws frame,
    run primitive (S fuel) nonpositive_branch
      (VInt balance :: VNat amount :: state :: bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match run primitive fuel empty_guard (bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => run primitive fuel after_empty_guard (VInt balance :: VNat amount :: state :: s) | None => None end.
  Proof.
    intros. cbn [nonpositive_branch run Nat.add List.app List.length firstn skipn Nat.leb].
    destruct (run primitive fuel empty_guard
      (bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame)); reflexivity.
  Qed.
  Lemma nonpositive_choice_step : forall fuel balance amount state handle token ds ws frame,
    run primitive (2 + S fuel)%nat after_empty_guard
      (VInt balance :: VNat amount :: state :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match run primitive (S fuel) (if Z.ltb balance 0 then incoming_case else [Drop])
      (VNat amount :: state :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Lemma incoming_build_step : forall fuel amount state handle token ds ws frame,
    run primitive (2 + S fuel)%nat incoming_case
      (VNat amount :: state :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    match (match run primitive (S fuel) build_in
      (VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
    | Some s => Some (state :: s) | None => None end) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Lemma zero_drop_step : forall fuel state handle token ds ws frame,
    run primitive (2 + fuel)%nat [Drop]
      (VNat 0 :: state :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair (VList ds) (VList ws) :: frame).
  Proof. reflexivity. Qed.

  Lemma verify_step : forall fuel tx old rest,
    run primitive (S fuel) iteration (tx :: old :: rest) =
    match primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) with
    | Some s => run primitive fuel (tl iteration) s | None => None end.
  Proof. reflexivity. Qed.
  Lemma numeric_step : forall fuel bound balance state rest,
    run primitive (9 + S fuel)%nat (tl iteration)
      (VSome (VPair bound (VPair (VInt balance) state)) :: rest) =
    match run primitive (S fuel) (if Z.gtb balance 0 then positive_branch else nonpositive_branch)
      (VInt balance :: VNat (Z.to_nat (Z.abs balance)) :: state :: bound :: rest) with
    | Some s => Some s | None => None end.
  Proof. reflexivity. Qed.
  Local Opaque run.

  Theorem address_guard_passes : forall padding bound recipient rest,
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    run primitive (12 + padding)%nat address_guard (bound :: rest) = Some (recipient :: rest).
  Proof.
    intros padding bound recipient rest HU HP.
    rewrite (address_unpack_step (11 + padding)%nat).
    rewrite (unpack_some_frame bound recipient) by exact HU.
    rewrite (address_pack_step (8 + padding)%nat), pack_frame.
    rewrite (address_compare_step (4 + padding)%nat), HP, Nat.compare_refl.
    apply (address_if_good (2 + padding)%nat).
  Qed.

  Theorem builds_outgoing_operation : forall padding amount recipient handle token ds ws frame,
    run primitive (18 + padding)%nat build_out
      (VNat amount :: recipient :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (handle :: token :: VPair (VList ds)
      (VList (make_operation (VPair self (VPair recipient (VNat amount))) handle :: ws)) :: frame).
  Proof.
    intros padding amount recipient handle token ds ws frame.
    rewrite (out_self_step (16 + padding)%nat), self_frame,
      (transfer_step (10 + padding)%nat), operation_frame.
    apply (append_out_step padding).
  Qed.

  Theorem builds_incoming_operation : forall padding amount handle token ds ws frame,
    run primitive (18 + padding)%nat build_in
      (VNat amount :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (handle :: token :: VPair
      (VList (make_operation (VPair sender (VPair self (VNat amount))) handle :: ds)) (VList ws) :: frame).
  Proof.
    intros padding amount handle token ds ws frame.
    rewrite (in_self_step (17 + padding)%nat), self_frame,
      (in_sender_step (16 + padding)%nat), sender_frame,
      (transfer_step (10 + padding)%nat), operation_frame.
    apply (append_in_step padding).
  Qed.

  Theorem positive_branch_updates : forall padding balance amount state bound recipient handle token ds ws frame,
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    run primitive (22 + padding)%nat positive_branch
      (VInt balance :: VNat amount :: state :: bound :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair (VList ds)
      (VList (make_operation (VPair self (VPair recipient (VNat amount))) handle :: ws)) :: frame).
  Proof.
    intros padding balance amount state bound recipient handle token ds ws frame HU HP.
    rewrite (positive_guard_step (20 + padding)%nat).
    rewrite (address_guard_passes (8 + padding)%nat bound recipient) by assumption.
    rewrite (positive_build_step (17 + padding)%nat), (builds_outgoing_operation padding). reflexivity.
  Qed.

  Theorem negative_branch_updates : forall padding balance amount state handle token ds ws frame,
    balance < 0 ->
    run primitive (24 + padding)%nat nonpositive_branch
      (VInt balance :: VNat amount :: state :: VBytes [] :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair
      (VList (make_operation (VPair sender (VPair self (VNat amount))) handle :: ds)) (VList ws) :: frame).
  Proof.
    intros padding balance amount state handle token ds ws frame HB.
    assert (HL : Z.ltb balance 0 = true) by (apply Z.ltb_lt; lia).
    rewrite (nonpositive_guard_step (23 + padding)%nat), (empty_guard_good (16 + padding)%nat).
    rewrite (nonpositive_choice_step (20 + padding)%nat), HL.
    rewrite (incoming_build_step (18 + padding)%nat), (builds_incoming_operation (1 + padding)%nat). reflexivity.
  Qed.

  Theorem zero_branch_updates : forall padding state handle token ds ws frame,
    run primitive (24 + padding)%nat nonpositive_branch
      (VInt 0 :: VNat 0 :: state :: VBytes [] :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair (VList ds) (VList ws) :: frame).
  Proof.
    intros padding state handle token ds ws frame.
    rewrite (nonpositive_guard_step (23 + padding)%nat), (empty_guard_good (16 + padding)%nat).
    rewrite (nonpositive_choice_step (20 + padding)%nat).
    change ((match run primitive (21 + padding)%nat [Drop]
      (VNat 0 :: state :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
      Some s => Some s | None => None end) =
      Some (state :: handle :: token :: VPair (VList ds) (VList ws) :: frame)).
    rewrite (zero_drop_step (19 + padding)%nat). reflexivity.
  Qed.

  Theorem verified_positive_iteration_128 :
    forall tx old bound balance state recipient handle token ds ws frame,
    verify tx old = Some (bound, balance, state) -> 0 < balance ->
    unpack bound = Some recipient -> List.length (pack recipient) = 28%nat ->
    run primitive 128 iteration (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair (VList ds)
      (VList (make_operation (VPair self (VPair recipient (VNat (Z.to_nat balance)))) handle :: ws)) :: frame).
  Proof.
    intros tx old bound balance state recipient handle token ds ws frame HV HB HU HP.
    assert (HG : Z.gtb balance 0 = true) by (apply Z.gtb_lt; lia).
    assert (HA : Z.to_nat (Z.abs balance) = Z.to_nat balance) by (rewrite Z.abs_eq; lia).
    rewrite (verify_step 127), (verify_some_frame tx old bound balance state) by exact HV.
    rewrite (numeric_step 117), HG, HA.
    rewrite (positive_branch_updates 96 balance (Z.to_nat balance) state bound recipient) by assumption. reflexivity.
  Qed.

  Theorem verified_negative_iteration_128 : forall tx old balance state handle token ds ws frame,
    verify tx old = Some (VBytes [], balance, state) -> balance < 0 ->
    run primitive 128 iteration (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair
      (VList (make_operation (VPair sender (VPair self (VNat (Z.to_nat (Z.abs balance))))) handle :: ds)) (VList ws) :: frame).
  Proof.
    intros tx old balance state handle token ds ws frame HV HB.
    assert (HG : Z.gtb balance 0 = false).
    { destruct (Z.gtb balance 0) eqn:HT; [apply Z.gtb_lt in HT; lia | reflexivity]. }
    rewrite (verify_step 127), (verify_some_frame tx old (VBytes []) balance state) by exact HV.
    rewrite (numeric_step 117), HG, (negative_branch_updates 94) by exact HB. reflexivity.
  Qed.

  Theorem verified_zero_iteration_128 : forall tx old state handle token ds ws frame,
    verify tx old = Some (VBytes [], 0, state) ->
    run primitive 128 iteration (tx :: old :: handle :: token :: VPair (VList ds) (VList ws) :: frame) =
    Some (state :: handle :: token :: VPair (VList ds) (VList ws) :: frame).
  Proof.
    intros tx old state handle token ds ws frame HV.
    rewrite (verify_step 127), (verify_some_frame tx old (VBytes []) 0 state) by exact HV.
    rewrite (numeric_step 117).
    change ((match run primitive 118 nonpositive_branch
      (VInt 0 :: VNat 0 :: state :: VBytes [] :: handle :: token :: VPair (VList ds) (VList ws) :: frame) with
      Some s => Some s | None => None end) =
      Some (state :: handle :: token :: VPair (VList ds) (VList ws) :: frame)).
    rewrite (zero_branch_updates 94). reflexivity.
  Qed.
End FA12Body.

Print Assumptions verified_positive_iteration_128.
Print Assumptions verified_negative_iteration_128.
Print Assumptions verified_zero_iteration_128.
