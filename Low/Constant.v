From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
Require Import stdpp.list.
Open Scope Z.

Module Low.

Definition C_121665 :list Z := [ 56129; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 ].
Definition C_0 := [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Definition C_1 := [1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0].
Definition C_25519 := [65517;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;32767].

End Low.

(* Eval compute in ZofList 16 c_121665. *)

Lemma C_121665_bounds : Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) Low.C_121665.
Proof. unfold Low.C_121665;
repeat match goal with
  | _ => change (2^16) with 65536 ; omega
  | |- _ /\ _ => split
  | _ => apply Forall_cons
  | _ => apply Forall_nil ; trivial
end.
Qed.

Lemma Zlength_c_121665 : Zlength Low.C_121665 = 16.
Proof. go. Qed.
Close Scope Z.

Lemma length_c_121665 : length Low.C_121665 = 16.
Proof. go. Qed.

Open Scope Z.

Lemma list_of_P: forall l,
  l = Low.C_25519 ->
  (ZofList 16 l) = Z.pow 2 255 - 19.
Proof. intros; subst; compute ; reflexivity. Qed.

Lemma Zlength_nul16 : Zlength Low.C_0 = 16.
Proof. go. Qed.
Lemma Zlength_One16 : Zlength Low.C_1 = 16.
Proof. go. Qed.
Lemma One16_bounds : Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) Low.C_1.
Proof. unfold Low.C_1;
repeat match goal with
  | _ => change (2^16) with 65536 ; omega
  | |- _ /\ _ => split
  | _ => apply Forall_cons
  | _ => apply Forall_nil ; trivial
end.
Qed.
Lemma nul16_bounds : Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) Low.C_0.
Proof. unfold Low.C_0;
repeat match goal with
  | _ => change (2^16) with 65536 ; omega
  | |- _ /\ _ => split
  | _ => apply Forall_cons
  | _ => apply Forall_nil ; trivial
end.
Qed.

Close Scope Z.