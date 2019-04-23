Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp_Ring.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
Import BinInt.

Require Import Ring.
Open Scope ring_scope.
Import GRing.Theory.

Definition a : Zmodp.type := Zmodp.pi 486662.
Definition b : Zmodp.type := 1%R.

Lemma asq_neq4 : a^+2 != 4%:R.
Proof. by rewrite expr2 ; zmodp_compute. Qed.

Lemma b_neq0 : b != 0.
Proof. exact: oner_neq0. Qed.

Canonical Structure curve25519_mcuType := Build_mcuType b_neq0 asq_neq4.

Lemma curve25519_chi2 : 2%:R != 0 :> Zmodp.type.
Proof. by zmodp_compute. Defined.

Lemma curve25519_chi3 : 3%:R != 0 :> Zmodp.type.
Proof. by zmodp_compute. Defined.

Definition curve25519_ecuFieldMixin :=
  ECUFieldMixin curve25519_chi2 curve25519_chi3.
Canonical Structure curve25519_ecuFieldType :=
  Eval hnf in ECUFieldType Zmodp.type curve25519_ecuFieldMixin.
Canonical Structure curve25519_finECUFieldType :=
  Eval hnf in [finECUFieldType of Zmodp.type].

Definition curve25519_ladder n x :=
  @opt_montgomery curve25519_finECUFieldType curve25519_mcuType n 255 x.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Theorem curve25519_ladder_ok (n : nat) x :
    (n < 2^255)%nat -> x != 0 ->
    forall (p : mc curve25519_mcuType), p#x0 = x -> curve25519_ladder n x = (p *+ n)#x0.
Proof.
move => Hn Hx p Hp.
rewrite /curve25519_ladder.
apply opt_montgomery_ok=> //=.
rewrite /a.
apply a_not_square.
Qed.
