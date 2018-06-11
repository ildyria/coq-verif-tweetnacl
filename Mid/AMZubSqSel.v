Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Mid.Car25519.

Open Scope Z.

Definition A a b := Z.add a b.
Definition M a b := Zcar25519 (Zcar25519 (Z.mul a b)).
Definition Zub a b := Z.sub a b.
Definition Sq a := M a a.
Definition c_121665 := 121665.
Definition Sel25519 (b p q:Z) :=   if (Z.eqb b 0) then p else q.

Lemma A_mod_eq : forall p q,
Z.modulo (A p q) (2 ^ 255 - 19) = Z.modulo (A (Z.modulo p (2 ^ 255 - 19)) (Z.modulo q (2 ^ 255 - 19))) (2 ^ 255 - 19).
Proof.
intros p q.
rewrite /A.
rewrite Z.add_mod.
reflexivity.
compute ; go.
Qed.

Lemma M_mod_eq : forall p q,
Z.modulo (M p q) (2 ^ 255 - 19) = Z.modulo (M (Z.modulo p (2 ^ 255 - 19)) (Z.modulo q (2 ^ 255 - 19))) (2 ^ 255 - 19).
Proof.
intros p q.
rewrite /M.
rewrite -?Zcar25519_correct.
rewrite Z.mul_mod.
reflexivity.
compute ; go.
Qed.

Lemma Zub_mod_eq : forall p q,
Z.modulo (Zub p q) (2 ^ 255 - 19) = Z.modulo (Zub (Z.modulo p (2 ^ 255 - 19)) (Z.modulo q (2 ^ 255 - 19))) (2 ^ 255 - 19).
Proof.
intros p q.
rewrite /Zub.
rewrite Zminus_mod.
reflexivity.
Qed.

Lemma Sq_mod_eq : forall p,
Z.modulo (Sq p) (2 ^ 255 - 19) = Z.modulo (Sq (Z.modulo p (2 ^ 255 - 19))) (2 ^ 255 - 19).
Proof.
intros p.
rewrite /Sq /M.
rewrite -?Zcar25519_correct.
rewrite Z.mul_mod.
reflexivity.
compute ; go.
Qed.

Close Scope Z.