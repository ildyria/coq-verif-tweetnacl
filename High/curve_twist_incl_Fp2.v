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
From Tweetnacl.High Require Import Zmodp2_rules.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_eq.
From Tweetnacl.High Require Import curve_incl_Fp2.
From Tweetnacl.High Require Import twist_incl_Fp2.
From Tweetnacl.High Require Import Zmodp.
Require Import Ring.
Require Import ZArith.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Local Lemma oncurve_00 : (oncurve curve25519_Fp2_mcuType (EC_In 0 0)).
Proof.
  simpl; rewrite /a /b ; apply/eqP.
  have ->: (0 ^+ 2)%R = 0 :> Zmodp2.type by ring_simplify_this.
  have ->: (0 ^+ 3)%R = 0 :> Zmodp2.type by ring_simplify_this.
  rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
  f_equal; f_equal; apply/eqP ; zmodp_compute => //=.
Qed.

Local Lemma oncurve25519 : forall x k k0 : Zmodp.type,
curve25519.b * k0 ^+ 2 == k ^+ 3 + curve25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have : oncurve curve25519_mcuType (EC_In k k') => //.
move/oncurve25519_impl => HOC.
exists (MC HOC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Local Lemma ontwist25519 : forall x k k0 : Zmodp.type,
twist25519.b * k0 ^+ 2 == k ^+ 3 + twist25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have : oncurve twist25519_mcuType (EC_In k k') => //.
move/ontwist25519_impl => HOC.
exists (MC HOC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

(* May actually not be in the right direction... *)
Theorem x_is_on_curve_or_twist_implies_x_in_Fp2: forall (x:Zmodp.type),
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

Definition Fp_to_Fp2 p := match p with
  | Zmodp2.Zmodp2 x y => x
  end.

Lemma Fp_to_Fp2_eq_C: Fp_to_Fp2 = cFp_to_Fp2.
Proof. reflexivity. Qed.

Lemma Fp_to_Fp2_eq_T: Fp_to_Fp2 = tFp_to_Fp2.
Proof. reflexivity. Qed.

Local Notation "p '/p'" := (Fp_to_Fp2 p) (at level 40).

Lemma Fp2_to_Fp :
  forall (x: Zmodp.type) (p : mc curve25519_Fp2_mcuType),
  p #x0 = Zmodp2.Zmodp2 x 0 ->
  (exists c:mc curve25519_mcuType, curve25519_Fp_to_Fp2 c = p) \/ (exists t:mc twist25519_mcuType, twist25519_Fp_to_Fp2 t = p).
Proof.
  move => x [[|xp yp] Hp].
  + (* is p is at infinity *)
  move => _ ; left.
  have Hc : oncurve curve25519_mcuType ∞ => //=.
  exists (MC Hc) => /= ; apply mc_eq => //.
  + (* if p is (x,y) *)
  have := Hp.
  rewrite /oncurve /= /a /b.
  destruct yp as [yp1 yp2].
  move => Hp' Hx.
  have : (Zmodp2.Zmodp2 yp1 yp2) ^+ 2 == (Zmodp2.Zmodp2 x 0) ^+ 3 + Zmodp2.pi (Zmodp.pi 486662, 0) * (Zmodp2.Zmodp2 x 0) ^+ 2 + (Zmodp2.Zmodp2 x 0).
  rewrite -Hx -(GRing.mul1r (Zmodp2.Zmodp2 yp1 yp2 ^+ 2)) //.
  rewrite expr3 ?expr2.
  Zmodpify => /=.
  have ->: Zmodp2.Zmodp2 yp1 yp2 * Zmodp2.Zmodp2 yp1 yp2 = Zmodp2.Zmodp2 (yp1^+2 + 2%:R * yp2^+2) (2%:R * yp1 * yp2).
  rewrite /GRing.mul /= /Zmodp2.mul /Zmodp2.pi expr2 /=.
  ringify .
  f_equal.
  rewrite /GRing.mul /= (Zmodp_ring.mul_comm yp2).
  symmetry.
  rewrite -Zmodp_ring.mul_assoc.
  ringify.
  apply add_eq_mul2.
  move/eqP.
  move/Zmodp2.Zmodp2_inv => [].
  ringify.
  move => Hxy.
  rewrite -GRing.mulrA.
  move/time_2_eq_0/mult_xy_eq_0 => [] Hy; rewrite Hy in Hxy;
  move: Hxy ; ring_simplify_this => Hxy.
  - right.
  have OC : oncurve twist25519_mcuType (| x, yp2 |).
    by apply/eqP => /= ; rewrite /twist25519.a /twist25519.b ?expr2 ?expr3' ; ringify.
  exists (MC OC) => /=.
  apply mc_eq ; congruence.
  - left.
  have OC : oncurve curve25519_mcuType (| x, yp1 |).
    by apply/eqP => /= ; rewrite /curve25519.a /curve25519.b ?expr2 ?expr3' mul1r; ringify.
  exists (MC OC) => /=.
  apply mc_eq ; congruence.
Qed.

From mathcomp Require Import ssrnat.

Lemma curve25519_ladder_maybe_ok (n : nat) (x:Zmodp.type) :
    (n < 2^255)%nat ->
    forall (p  : mc curve25519_Fp2_mcuType),
    p #x0 = Zmodp2.Zmodp2 x 0 ->
    curve25519_ladder n x = (p *+ n)#x0 /p.
Proof.
  move => Hn p Hp.
  have /orP[Hx|Hx] := orNb (x == 0).
  + have [[c] Hc|[t] Ht] := Fp2_to_Fp x p Hp.
    + have Hcx0: curve25519_Fp_to_Fp2 c #x0 = Zmodp2.Zmodp2 x 0 by rewrite Hc.
      rewrite (curve25519_ladder_really_ok n x Hn Hx c Hcx0) -Fp_to_Fp2_eq_C Hc //.
    + have Htx0: twist25519_Fp_to_Fp2 t #x0 = Zmodp2.Zmodp2 x 0 by rewrite Ht.
      rewrite curve_twist_eq.
      rewrite (twist25519_ladder_really_ok n x Hn Hx t Htx0) -Fp_to_Fp2_eq_T Ht //.
  + move/eqP: Hx Hp => ->.
    rewrite curve25519_0.
    have -> : Zmodp2.Zmodp2 0 0 = 0 => //=.
    move/(p_x0_0_eq_0 n) => -> //.
Qed.

Close Scope ring_scope.