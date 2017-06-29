Require Import Tweetnacl.Libs.Export.
Require Import stdpp.prelude.

Open Scope Z.

Definition set_xor (i:Z) := Z.lnot (i - 1).

(*
Eval compute in (set_xor 0).
Eval compute in (set_xor 1).
*)

Lemma set_xor_0 : set_xor 0 = 0.
Proof. reflexivity. Qed.

Lemma set_xor_1 : set_xor 1 = -1.
Proof. reflexivity. Qed.

Lemma land_0 : forall i, Z.land 0 i = 0.
Proof. intro. go. Qed.

Lemma land_minus_1 : forall i, Z.land (-1) i = i.
Proof. intro. apply Z.land_m1_l. Qed.

Close Scope Z.
