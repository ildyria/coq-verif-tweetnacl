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
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp_Ring.
Require Import ZArith.

Import BinInt.
Open Scope ring_scope.
Import GRing.Theory.

Theorem curve_twist_eq: forall n x, 
  curve25519_ladder n x = twist25519_ladder n x.
Proof.
move => n x.
rewrite /curve25519_ladder /twist25519_ladder  /opt_montgomery.
elim 255 => //.
Qed.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Lemma x_is_on_curve_or_twist: forall x,
  (exists (p : mc curve25519_mcuType), p#x0 = x) \/
  (exists (p' : mc twist25519_mcuType), p'#x0 = x).
Proof.
move => x.
have := x_square_minus_x (x^+3 + (Zmodp.pi 486662) *  x^+2 + x)%R.
move => [] y [Hy|Hy] ; [left|right].
+{
  have OC : (oncurve curve25519_mcuType (EC_In x y)).
  simpl; rewrite /curve25519.b /curve25519.a.
  have ->: (1 * y ^+ 2 = y ^+ 2)%R by apply Zmodp_ring.mul_left_id.
  apply/eqP => //.
  exists (MC OC) => //.
 }
+{
  have OC : (oncurve twist25519_mcuType (EC_In x y)).
  simpl; rewrite /b /a.
  apply/eqP => //.
  exists (MC OC) => //.
 }
Qed.

