From Tweetnacl Require Import Libs.Export.
Require Import stdpp.prelude.
Open Scope Z.

Definition c_121665 :list Z := [ 56129; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0 ].

Lemma c_121665_bounds : Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) c_121665.
Proof. unfold c_121665;
repeat match goal with
  | _ => change (2^16) with 65536 ; omega
  | |- _ /\ _ => split
  | _ => apply Forall_cons
  | _ => apply Forall_nil ; trivial
end.
Qed.

Lemma Zlength_c_121665 : Zlength c_121665 = 16.
Proof. go. Qed.
Close Scope Z.

Lemma length_c_121665 : length c_121665 = 16.
Proof. go. Qed.