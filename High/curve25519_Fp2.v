Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.
Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Definition a : Zmodp2.type := Zmodp2.pi (Zmodp.pi 486662, 0).
Definition b : Zmodp2.type := Zmodp2.pi (1, 0).

Lemma b_neq0 : b != 0.
Proof. exact: oner_neq0. Qed.

Lemma asq_neq4 : (a ^+ 2 != 4%:R).
Proof.
rewrite expr2 /a.
change (Zmodp2.piZ (486662, 0%Z)) with (Zmodp2.pi (Zmodp.pi 486662, Zmodp.pi 0)).
rewrite Zmodp2_mulE /=.
apply/eqP => H.
inversion H ; clear H.
move/eqP: H1.
zmodp_compute.
move/eqP => H.
inversion H.
Qed.

Canonical Structure curve25519_Fp2_mcuType := Build_mcuType b_neq0 asq_neq4.

Lemma curve25519_Fp2_chi2 : 2%:R != 0 :> Zmodp2.type.
Proof.
simpl.
have -> : 2%:R = Zmodp2.one + Zmodp2.one :> Zmodp2.type by rewrite Zmodp2_addE.
apply Zmodp2_ring.two_neq_zero.
Qed.

Lemma curve25519_Fp2_chi3 : 3%:R != 0 :> Zmodp2.type.
Proof.
have -> : 3%:R = Zmodp2.one + Zmodp2.one + Zmodp2.one :> Zmodp2.type.
2: apply Zmodp2_ring.three_neq_zero.
by apply/eqP; zmodp2_compute; zmodp_compute; apply/andP; split; zmodp_compute.
Qed.

Definition curve25519_Fp2_ecuFieldMixin :=
  ECUFieldMixin curve25519_Fp2_chi2 curve25519_Fp2_chi3.
Canonical Structure curve25519_Fp2_ecuFieldType :=
  Eval hnf in ECUFieldType Zmodp2.type curve25519_Fp2_ecuFieldMixin.
Canonical Structure curve25519_Fp2_finECUFieldType :=
  Eval hnf in [finECUFieldType of Zmodp2.type].
