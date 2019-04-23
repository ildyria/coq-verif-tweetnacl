Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
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
change (Zmodp.pi 0) with Zmodp.zero.
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

Definition curve25519_Fp2_ladder n x :=
  @opt_montgomery curve25519_Fp2_finECUFieldType curve25519_Fp2_mcuType n 255 x.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Theorem curve25519_Fp2_ladder_ok (n : nat) (x : Zmodp.type) :
    (n < 2^255)%nat -> x != 0 ->
    forall (p : mc curve25519_Fp2_mcuType), p#x0 = Zmodp2.pi (x, Zmodp.zero) -> curve25519_Fp2_ladder n (Zmodp2.pi (x, Zmodp.zero)) = (p *+ n)#x0.
Proof.
move => Hn Hx p Hp.
rewrite /curve25519_Fp2_ladder.
apply opt_montgomery_ok=> //=.
2: by apply/eqP => H ; inversion H ; subst.
Admitted.
(* apply curve25519_residute. *)
(* Qed. *)
