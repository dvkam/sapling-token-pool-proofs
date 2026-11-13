From Coq Require Import List ZArith String.
Require Import FullVM_WIP.
Import ListNotations.
Open Scope string_scope.

(* A single callback environment shared by both FA2 branches. The callbacks
   specify an interface; their correspondence to Octez/Sapling/token behavior
   and to a concrete finite map remains an external proof obligation. *)
Section Environment.
  Variable verify : value -> value -> option (value * Z * value).
  Variable unpack : value -> option value.
  Variable pack : value -> list nat.
  Variable sender : value.
  Variable lookup : value -> value -> option nat.
  Variable update : value -> option nat -> value -> value.
  Variable other : string -> stack -> option stack.

  Definition primitive (name : string) (s : stack) : option stack :=
    match name, s with
    | "SAPLING_VERIFY_UPDATE", tx :: old_state :: rest =>
        Some ((match verify tx old_state with
          | None => VNone
          | Some (bound, balance, new_state) => VSome (VPair bound (VPair (VInt balance) new_state))
          end) :: rest)
    | "UNPACK_address", bound :: rest =>
        Some ((match unpack bound with None => VNone | Some recipient => VSome recipient end) :: rest)
    | "PACK_address", recipient :: rest => Some (VBytes (pack recipient) :: rest)
    | "SENDER", _ => Some (sender :: s)
    | "GET", key :: map :: rest =>
        Some ((match lookup key map with None => VNone | Some n => VSome (VNat n) end) :: rest)
    | "UPDATE", key :: VSome (VNat amount) :: map :: rest =>
        Some (update key (Some amount) map :: rest)
    | "UPDATE", key :: VNone :: map :: rest => Some (update key None map :: rest)
    | _, _ => other name s
    end.

  Lemma sender_frame : forall s, primitive "SENDER" s = Some (sender :: s).
  Proof. reflexivity. Qed.
  Lemma verify_frame : forall tx old rest,
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old :: rest) =
    Some ((match verify tx old with
      | None => VNone
      | Some (bound, balance, new_state) => VSome (VPair bound (VPair (VInt balance) new_state))
      end) :: rest).
  Proof. reflexivity. Qed.
  Lemma unpack_frame : forall bound rest,
    primitive "UNPACK_address" (bound :: rest) =
    Some ((match unpack bound with None => VNone | Some recipient => VSome recipient end) :: rest).
  Proof. reflexivity. Qed.
  Lemma pack_frame : forall recipient rest,
    primitive "PACK_address" (recipient :: rest) = Some (VBytes (pack recipient) :: rest).
  Proof. reflexivity. Qed.
  Lemma get_frame : forall key map rest,
    primitive "GET" (key :: map :: rest) =
    Some ((match lookup key map with None => VNone | Some n => VSome (VNat n) end) :: rest).
  Proof. reflexivity. Qed.
  Lemma update_frame : forall key amount map rest,
    primitive "UPDATE" (key :: VSome (VNat amount) :: map :: rest) =
    Some (update key (Some amount) map :: rest).
  Proof. reflexivity. Qed.
End Environment.
