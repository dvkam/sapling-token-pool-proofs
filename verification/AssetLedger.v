(* SPDX-License-Identifier: MIT *)
From Coq Require Import List ZArith String Lia.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

(* Ledger projection for ONE configured asset. These functions do not grant
   authorization or claim that every mathematical move can execute. A successful
   honest issuer must have this debit-then-credit projection; its own policy,
   fees in other assets and actual execution are separate specifications. *)
Record transfer := Transfer { from_account : value; to_account : value; units : nat }.
Definition ledger := value -> Z.

Section Ledger.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Definition set_balance (l : ledger) (account : value) (amount : Z) : ledger :=
    fun queried => if eq_value queried account then amount else l queried.
  Definition move (l : ledger) (t : transfer) : ledger :=
    let debited := set_balance l (from_account t) (l (from_account t) - Z.of_nat (units t)) in
    set_balance debited (to_account t) (debited (to_account t) + Z.of_nat (units t)).
  Definition reserve_delta (pool : value) (t : transfer) : Z :=
    (if eq_value pool (to_account t) then Z.of_nat (units t) else 0) -
    (if eq_value pool (from_account t) then Z.of_nat (units t) else 0).
  Fixpoint net_delta (pool : value) (ts : list transfer) : Z :=
    match ts with [] => 0 | t :: rest => reserve_delta pool t + net_delta pool rest end.
  Fixpoint settle (ts : list transfer) (l : ledger) : ledger :=
    match ts with [] => l | t :: rest => settle rest (move l t) end.

  Theorem move_reserve_effect : forall l from to amount pool,
    move l (Transfer from to amount) pool = l pool + reserve_delta pool (Transfer from to amount).
  Proof.
    intros. unfold move, set_balance, reserve_delta. cbn [from_account to_account units].
    repeat match goal with |- context [eq_value ?x ?y] => destruct (eq_value x y); subst; try contradiction end;
      try congruence; lia.
  Qed.

  Theorem self_transfer_preserves_every_balance : forall l account amount queried,
    move l (Transfer account account amount) queried = l queried.
  Proof.
    intros. rewrite move_reserve_effect. unfold reserve_delta. cbn [from_account to_account units].
    destruct (eq_value queried account); lia.
  Qed.

  Lemma deposit_delta : forall sender pool amount, sender <> pool ->
    reserve_delta pool (Transfer sender pool amount) = Z.of_nat amount.
  Proof.
    intros. unfold reserve_delta. cbn [from_account to_account units].
    destruct (eq_value pool pool); [|contradiction]. destruct (eq_value pool sender); [congruence|lia].
  Qed.
  Lemma withdrawal_delta : forall pool recipient amount,
    reserve_delta pool (Transfer pool recipient amount) =
    - Z.of_nat amount + (if eq_value pool recipient then Z.of_nat amount else 0).
  Proof.
    intros. unfold reserve_delta. cbn [from_account to_account units].
    destruct (eq_value pool pool); [|contradiction]. destruct (eq_value pool recipient); lia.
  Qed.
  Lemma withdrawal_delta_lower_bound : forall pool recipient amount,
    - Z.of_nat amount <= reserve_delta pool (Transfer pool recipient amount).
  Proof. intros; rewrite withdrawal_delta; destruct (eq_value pool recipient); lia. Qed.
  Lemma net_delta_app : forall pool left right,
    net_delta pool (left ++ right) = net_delta pool left + net_delta pool right.
  Proof. intros pool left; induction left; intros; cbn [app net_delta]; [lia|rewrite IHleft; lia]. Qed.
  Lemma net_delta_rev : forall pool ts, net_delta pool (rev ts) = net_delta pool ts.
  Proof.
    intros pool ts; induction ts; cbn [rev net_delta]; [reflexivity|].
    rewrite net_delta_app, IHts. cbn [net_delta]; lia.
  Qed.
  Theorem settlement_reserve_effect : forall ts l pool,
    settle ts l pool = l pool + net_delta pool ts.
  Proof.
    induction ts as [|t ts IH]; intros; cbn [settle net_delta]; [lia|].
    destruct t as [from to amount]. rewrite IH, move_reserve_effect; lia.
  Qed.
  Theorem pending_settlement_potential : forall l pool liability t pending,
    move l t pool + net_delta pool pending - liability =
    l pool + net_delta pool (t :: pending) - liability.
  Proof. intros; destruct t; rewrite move_reserve_effect; cbn [net_delta]; lia. Qed.

  Theorem liability_entry_preserves_pending_potential :
    forall pool reserve old_liability new_liability emitted pending,
    new_liability - old_liability <= net_delta pool emitted ->
    reserve + net_delta pool pending - old_liability <=
    reserve + net_delta pool (emitted ++ pending) - new_liability.
  Proof. intros; rewrite net_delta_app; lia. Qed.

  (* Pointwise state relation avoids adding functional extensionality. *)
  Lemma move_respects_ledger_projection : forall l1 l2 t,
    (forall account, l1 account = l2 account) -> forall account, move l1 t account = move l2 t account.
  Proof.
    intros l1 l2 [from to amount] H account. unfold move, set_balance.
    cbn [from_account to_account units]. rewrite !H. reflexivity.
  Qed.

  Section HonestIssuer.
    Variable state : Type.
    Variable balances : state -> ledger.
    Variable policy : state -> transfer -> Prop.
    Variable applied : state -> transfer -> state -> Prop.
    Hypothesis successful_issuer_projection : forall before t after,
      applied before t after -> policy before t /\
      forall account, balances after account = move (balances before) t account.
    Inductive issuer_trace : state -> list transfer -> state -> Prop :=
    | issuer_nil : forall s, issuer_trace s [] s
    | issuer_cons : forall before t middle ts after,
        applied before t middle -> issuer_trace middle ts after -> issuer_trace before (t :: ts) after.

    Theorem honest_issuer_trace_reserve_effect : forall before ts after,
      issuer_trace before ts after -> forall pool,
      balances after pool = balances before pool + net_delta pool ts.
    Proof.
      intros before ts after H; induction H; intros pool; cbn [net_delta]; [lia|].
      destruct (successful_issuer_projection _ _ _ H) as [_ HE].
      rewrite IHissuer_trace, HE. destruct t. rewrite move_reserve_effect. lia.
    Qed.
  End HonestIssuer.
End Ledger.

Definition fa12_parameter (t : transfer) :=
  VPair (from_account t) (VPair (to_account t) (VNat (units t))).
Definition decode_fa12_parameter (p : value) : option transfer :=
  match p with VPair from (VPair to (VNat amount)) => Some (Transfer from to amount) | _ => None end.
Lemma decode_fa12_exact : forall t, decode_fa12_parameter (fa12_parameter t) = Some t.
Proof. intros []; reflexivity. Qed.

Section DecodeCalls.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable operation : value -> value -> value.
  Variable decode_call : value -> option (value * value).
  Hypothesis operation_fields : forall parameter handle,
    decode_call (operation parameter handle) = Some (handle, parameter).
  Variable handle : value.
  Fixpoint decode_fa12_operations (ops : list value) : option (list transfer) :=
    match ops with
    | [] => Some []
    | op :: rest =>
        match decode_call op with
        | Some (target,p) => if eq_value target handle then
            match decode_fa12_parameter p, decode_fa12_operations rest with
            | Some t, Some ts => Some (t :: ts) | _, _ => None end
          else None
        | None => None end
    end.
  Lemma decode_fa12_cons : forall t ops ts,
    decode_fa12_operations ops = Some ts ->
    decode_fa12_operations (operation (fa12_parameter t) handle :: ops) = Some (t :: ts).
  Proof.
    intros. cbn [decode_fa12_operations]. rewrite operation_fields.
    destruct (eq_value handle handle); [|contradiction]. rewrite decode_fa12_exact, H. reflexivity.
  Qed.
  Lemma decode_fa12_app : forall left right ls rs,
    decode_fa12_operations left = Some ls -> decode_fa12_operations right = Some rs ->
    decode_fa12_operations (left ++ right) = Some (ls ++ rs).
  Proof.
    induction left as [|op left IH]; intros right ls rs HL HR; cbn [app decode_fa12_operations] in *.
    - inversion HL; subst. exact HR.
    - destruct (decode_call op) as [[target p]|]; [|discriminate].
      destruct (eq_value target handle); [|discriminate].
      destruct (decode_fa12_parameter p) as [t|]; [|discriminate].
      destruct (decode_fa12_operations left) as [tail|] eqn:HT; [|discriminate].
      inversion HL; subst ls. rewrite (IH right tail rs eq_refl HR). reflexivity.
  Qed.
  Lemma decode_fa12_rev : forall ops ts,
    decode_fa12_operations ops = Some ts -> decode_fa12_operations (rev ops) = Some (rev ts).
  Proof.
    induction ops as [|op ops IH]; intros ts H; cbn [decode_fa12_operations] in H.
    - inversion H; reflexivity.
    - destruct (decode_call op) as [[target p]|] eqn:HC; [|discriminate].
      destruct (eq_value target handle) as [HE|HE]; [|discriminate].
      destruct (decode_fa12_parameter p) as [t|] eqn:HP; [|discriminate].
      destruct (decode_fa12_operations ops) as [tail|] eqn:HT; [|discriminate].
      inversion H; subst ts. cbn [rev].
      eapply decode_fa12_app; [apply IH; reflexivity|].
      cbn [decode_fa12_operations]. rewrite HC. destruct (eq_value target handle); [|contradiction].
      rewrite HP. reflexivity.
  Qed.
End DecodeCalls.

Print Assumptions move_reserve_effect.
Print Assumptions settlement_reserve_effect.
Print Assumptions honest_issuer_trace_reserve_effect.
Print Assumptions decode_fa12_rev.

Section DecodeFA2.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable token_id : value.
  Fixpoint decode_fa2_items (from : value) (items : list value) : option (list transfer) :=
    match items with
    | [] => Some []
    | VPair to (VPair id (VNat q)) :: rest =>
        if eq_value id token_id then
          match decode_fa2_items from rest with
          | Some ts => Some (Transfer from to q :: ts) | None => None end
        else None
    | _ => None end.
  Fixpoint decode_fa2_groups (groups : list value) : option (list transfer) :=
    match groups with
    | [] => Some []
    | VPair from (VList items) :: rest =>
        match decode_fa2_items from items, decode_fa2_groups rest with
        | Some ts, Some remaining => Some (ts ++ remaining) | _, _ => None end
    | _ => None end.
  Definition decode_fa2_parameter p :=
    match p with VList groups => decode_fa2_groups groups | _ => None end.

  Definition fa2_items (xs : list (value * nat)) :=
    map (fun '(to,q) => VPair to (VPair token_id (VNat q))) xs.
  Definition movements (from : value) (xs : list (value * nat)) :=
    map (fun '(to,q) => Transfer from to q) xs.
  Lemma decode_fa2_items_exact : forall from xs,
    decode_fa2_items from (fa2_items xs) = Some (movements from xs).
  Proof.
    intros from xs; unfold fa2_items, movements.
    induction xs as [|[to q] xs IH]; cbn [map decode_fa2_items].
    - reflexivity.
    - destruct (eq_value token_id token_id); [now rewrite IH|contradiction].
  Qed.
  Lemma decode_fa2_groups_app : forall a b ats bts,
    decode_fa2_groups a = Some ats -> decode_fa2_groups b = Some bts ->
    decode_fa2_groups (a ++ b) = Some (ats ++ bts).
  Proof.
    induction a as [|g a IH]; intros b ats bts HA HB; cbn [app decode_fa2_groups] in *.
    - inversion HA; exact HB.
    - destruct g; try discriminate. destruct g2; try discriminate.
      match type of HA with context [decode_fa2_items ?from ?items] =>
        destruct (decode_fa2_items from items) as [ts|] eqn:HI end; [|discriminate].
      destruct (decode_fa2_groups a) as [rest|] eqn:HR; [|discriminate].
      inversion HA; subst ats. rewrite (IH b rest bts eq_refl HB), app_assoc. reflexivity.
  Qed.
  Definition fa2_deposit_groups pool (deposits : list (value * nat)) :=
    map (fun '(payer,q) => VPair payer (VList (fa2_items [(pool,q)]))) deposits.
  Definition deposit_movements pool (deposits : list (value * nat)) :=
    map (fun '(payer,q) => Transfer payer pool q) deposits.
  Lemma decode_fa2_deposit_groups_exact : forall pool deposits,
    decode_fa2_groups (fa2_deposit_groups pool deposits) = Some (deposit_movements pool deposits).
  Proof.
    intros pool deposits; unfold fa2_deposit_groups, deposit_movements.
    induction deposits as [|[payer q] deposits IH]; cbn [map decode_fa2_groups].
    - reflexivity.
    - rewrite decode_fa2_items_exact, IH. reflexivity.
  Qed.
  Theorem decode_fa2_deposit_first_parameter : forall pool deposits withdrawals,
    decode_fa2_parameter
      (VList (fa2_deposit_groups pool deposits ++ [VPair pool (VList (fa2_items withdrawals))])) =
    Some (deposit_movements pool deposits ++ movements pool withdrawals).
  Proof.
    intros. unfold decode_fa2_parameter. apply decode_fa2_groups_app.
    - apply decode_fa2_deposit_groups_exact.
    - cbn [decode_fa2_groups]. rewrite decode_fa2_items_exact, app_nil_r. reflexivity.
  Qed.
End DecodeFA2.
Print Assumptions decode_fa2_deposit_first_parameter.

Section DecodeFA2Calls.
  Variable eq_value : forall x y : value, {x = y} + {x <> y}.
  Variable token_id handle : value.
  Variable decode_call : value -> option (value * value).
  Fixpoint decode_fa2_operations (ops : list value) : option (list transfer) :=
    match ops with
    | [] => Some []
    | op :: rest => match decode_call op with
      | Some (target,p) => if eq_value target handle then
          match decode_fa2_parameter eq_value token_id p, decode_fa2_operations rest with
          | Some ts, Some remaining => Some (ts ++ remaining) | _,_ => None end
        else None
      | None => None end end.
  Variable operation : value -> value -> value.
  Hypothesis operation_fields : forall parameter target,
    decode_call (operation parameter target) = Some (target,parameter).
  Theorem decode_fa2_constructed_singleton : forall parameter ts,
    decode_fa2_parameter eq_value token_id parameter = Some ts ->
    decode_fa2_operations [operation parameter handle] = Some ts.
  Proof.
    intros. cbn [decode_fa2_operations]. rewrite operation_fields.
    destruct (eq_value handle handle); [|contradiction]. rewrite H, app_nil_r. reflexivity.
  Qed.
End DecodeFA2Calls.
Print Assumptions decode_fa2_constructed_singleton.
