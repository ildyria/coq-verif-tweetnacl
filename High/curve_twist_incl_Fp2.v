Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519.
From Tweetnacl.High Require Import twist25519.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_eq.
From Tweetnacl.High Require Import Zmodp.

Require Import ZArith.

Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "Z.R A" := (Zmodp.repr A) (at level 30).
Local Notation "-. A" := (Zmodp.opp A) (at level 30).

Local Lemma expr3 : forall x:Zmodp2.type, (x^+3 = x*x*x)%R.
Proof.
move => x; rewrite ?exprSr expr0 GRing.mul1r //.
Qed.

Local Lemma expr3' : forall x:Zmodp.type, (x^+3 = x*x*x)%R.
Proof.
move => x; rewrite ?exprSr expr0 GRing.mul1r //.
Qed.

Local Lemma oncurve_00 : (oncurve curve25519_Fp2_mcuType (EC_In 0 0)).
Proof.
  simpl; rewrite /a /b ; apply/eqP.
  have ->: (Zmodp2.piZ (1%Z, 0%Z)) = Zmodp2.pi (Zmodp.pi 1, Zmodp.pi 0) => //.
  have ->: (Zmodp2.piZ (486662%Z, 0%Z)) = Zmodp2.pi (Zmodp.pi 486662, Zmodp.pi 0) => //.
  have ->: (0 ^+ 2)%R = 0 :> Zmodp2.type by rewrite expr2 ?GRing.mulr0.
  have ->: (0 ^+ 3)%R = 0 :> Zmodp2.type by rewrite expr3 ?GRing.mulr0.
  rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
  f_equal; f_equal; apply/eqP ; zmodp_compute => //=.
Qed.


Local Lemma oncurve25519 : forall x k k0 : Zmodp.type,
curve25519.b * k0 ^+ 2 == k ^+ 3 + curve25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have OC: (oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (k, Zmodp.pi 0)) (Zmodp2.pi (k', Zmodp.pi 0)))) => /=.
rewrite /a /b.
have ->: (Zmodp2.piZ (1%Z, 0%Z)) = Zmodp2.pi (Zmodp.pi 1, Zmodp.pi 0) => //.
have ->: (Zmodp2.piZ (486662%Z, 0%Z)) = Zmodp2.pi (Zmodp.pi 486662, Zmodp.pi 0) => //.
rewrite ?expr2 ?expr3.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
move: Hx.
rewrite /curve25519.a /curve25519.b.
rewrite ?expr2 ?expr3'.
rewrite ?GRing.mul1r.
move/eqP.
move=> ->.
rewrite ?GRing.mul0r ?GRing.mulr0 ?GRing.addr0.
apply/eqP; f_equal ; f_equal.
rewrite /a /b.
exists (MC OC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Local Lemma ontwist25519 : forall x k k0 : Zmodp.type,
twist25519.b * k0 ^+ 2 == k ^+ 3 + twist25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have OC: (oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (k, Zmodp.pi 0)) (Zmodp2.pi (Zmodp.pi 0, k')))) => /=.
rewrite /a /b.
have ->: (Zmodp2.piZ (1%Z, 0%Z)) = Zmodp2.pi (Zmodp.pi 1, Zmodp.pi 0) => //.
have ->: (Zmodp2.piZ (486662%Z, 0%Z)) = Zmodp2.pi (Zmodp.pi 486662, Zmodp.pi 0) => //.
rewrite ?expr2 ?expr3.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
move: Hx.
rewrite /twist25519.b /twist25519.a.
rewrite ?expr2 ?expr3'.
rewrite ?GRing.mul1r.
move/eqP.
move=> ->.
rewrite ?GRing.mul0r ?GRing.mulr0 ?GRing.addr0 ?GRing.add0r.
apply/eqP; f_equal ; f_equal.
exists (MC OC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Lemma x_is_on_curve_or_twist_implies_x_in_Fp2: forall (x:Zmodp.type),
  exists (p: mc curve25519_Fp2_mcuType), p#x0 = Zmodp2.Zmodp2 x 0.
Proof.
  move=> x.
  have := x_is_on_curve_or_twist x.
  move=> [] [] [] [] /=.
  - move=> _ <- ; exists (MC oncurve_00) => //=.
  - apply oncurve25519.
  - move=> _ <- ; exists (MC oncurve_00) => //=.
  - apply ontwist25519.
Qed.
