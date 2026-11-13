From Coq Require Import List String.
Require Import FullVM_WIP FA2Operations FA2Map.
Import ListNotations.
Open Scope list_scope.

Lemma withdrawal_item_fuel : forall fuel prim recipient amount groups handle state token token_id frame,
  run prim (5 + fuel)%nat withdrawal_item_body
    (VPair recipient amount :: groups :: handle :: state :: token :: token_id :: frame) =
  Some (VPair recipient (VPair token_id amount) :: groups :: handle :: state :: token :: token_id :: frame).
Proof. reflexivity. Qed.

Lemma mapped_items_exact_fuel : forall fuel prim entries groups handle state token token_id frame,
  map_items prim (5 + fuel)%nat
    (List.map (fun entry => VPair (fst entry) (snd entry)) entries)
    (groups :: handle :: state :: token :: token_id :: frame) =
  Some (List.map (fun entry => VPair (fst entry) (VPair token_id (snd entry))) entries,
        groups :: handle :: state :: token :: token_id :: frame).
Proof.
  intros fuel prim entries; induction entries as [|[recipient amount] entries IH];
    intros groups handle state token token_id frame; cbn [List.map map_items].
  - reflexivity.
  - rewrite withdrawal_item_fuel, IH. reflexivity.
Qed.

Theorem unbounded_withdrawal_mapping_fuel :
  forall fuel prim entries groups handle state token token_id frame,
  run prim (6 + fuel)%nat [Map withdrawal_item_body]
    (VList (List.map (fun entry => VPair (fst entry) (snd entry)) entries) ::
     groups :: handle :: state :: token :: token_id :: frame) =
  Some (VList (List.map (fun entry => VPair (fst entry) (VPair token_id (snd entry))) entries) ::
        groups :: handle :: state :: token :: token_id :: frame).
Proof.
  intros; rewrite (map_step prim (4 + fuel)%nat).
  change (match map_items prim (5 + fuel)%nat
    (List.map (fun entry => VPair (fst entry) (snd entry)) entries)
    (groups :: handle :: state :: token :: token_id :: frame)
    with Some (ys, fin) => Some (VList ys :: fin) | None => None end =
    Some (VList (List.map (fun entry => VPair (fst entry) (VPair token_id (snd entry))) entries) ::
        groups :: handle :: state :: token :: token_id :: frame)).
  rewrite (mapped_items_exact_fuel fuel prim entries groups handle state token token_id frame); reflexivity.
Qed.
Print Assumptions unbounded_withdrawal_mapping_fuel.
