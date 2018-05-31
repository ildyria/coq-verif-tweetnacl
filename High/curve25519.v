Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype ssralg.
From Tweetnacl.High Require Import mc Zmodp opt_ladder.

Open Scope ring_scope.
Import GRing.Theory.

Definition a : Zmodp.type := Zmodp.pi 486662.
Definition b : Zmodp.type := 1%R.

Lemma asq_neq4 : a^+2 != 4%:R.
Proof. by rewrite expr2; zmodp_compute. Qed.

Lemma b_neq0 : b != 0.
Proof. exact: oner_neq0. Qed.

Canonical Structure curve25519_mcuType := Build_mcuType b_neq0 asq_neq4.

Lemma curve25519_chi2 : 2%:R != 0 :> Zmodp.type.
Proof. by zmodp_compute. Qed.

Lemma curve25519_chi3 : 3%:R != 0 :> Zmodp.type.
Proof. by zmodp_compute. Qed.

Definition curve25519_ecuFieldMixin :=
  ECUFieldMixin curve25519_chi2 curve25519_chi3.
Canonical Structure curve25519_ecuFieldType :=
  Eval hnf in ECUFieldType Zmodp.type curve25519_ecuFieldMixin.
Canonical Structure curve25519_finECUFieldType :=
  Eval hnf in [finECUFieldType of Zmodp.type].

Definition curve25519_ladder n x :=
  @opt_montgomery curve25519_finECUFieldType curve25519_mcuType n 255 x.
