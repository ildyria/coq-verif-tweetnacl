Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
Import BinInt.

Open Scope ring_scope.

Definition a : F_p2.type := F_p2.pi (486662,0).
Definition b : F_p2.type := (1,0)%R.

Lemma asq_neq4 : a^+2 != (4,0)%:R.
Proof. by rewrite expr2; zmodp_compute. Qed.

Lemma b_neq0 : b != 0.
Proof. exact: oner_neq0. Qed.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

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

Theorem Curve25519_Correct: (n : nat) (x: F_p) (p: mc curve25519_mcuType):
    (n < 2^255)%nat -> 
    p#x0 = x ->
    curve25519_ladder n x = (p *+ n)#x0.
