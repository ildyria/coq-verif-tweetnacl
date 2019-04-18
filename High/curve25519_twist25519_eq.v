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
From Tweetnacl.High Require Import Zmodp.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "Z.R A" := (Zmodp.repr A) (at level 30).
Local Notation "-. A" := (Zmodp.opp A) (at level 30).

Lemma x_square_minus_x: forall (x:Zmodp.type),
  exists (y:Zmodp.type), (y^+2 = x \/ (Zmodp.pi 2)* y^+2 = x)%R.
Proof.
  move => x.
  have Prime:(Znumtheory.prime Zmodp.p).
    rewrite /Zmodp.p -lock ; apply curve25519_numtheory_prime.
  have Prime2:= ZmodP_mod2_eq_1.
  replace (BinInt.Z.sub (BinInt.Z.pow 2 255) 19) with Zmodp.p in Prime2.
  2: rewrite /Zmodp.p -lock //.
  have Eulers_Criterion := Eulers_criterion Zmodp.p Prime Prime2 (Zmodp.repr x).
  rewrite /legendre in Eulers_Criterion.
  destruct (ClassicalDescription.excluded_middle_informative _).
  + exists Zmodp.zero.
    left.
    have ->: Zmodp.zero ^+2 = Zmodp.zero => //.
    move/modZp0/eqP:e -> => //.
  + destruct (ClassicalDescription.excluded_middle_informative _).
    move: e => [y Hy].
    exists (Zmodp.pi y).
    left.
    apply val_inj => /=.
    move: Hy.
    rewrite modZp => <-.
    rewrite Z.mul_mod_idemp_l; last by rewrite /p -lock.
    rewrite Z.mul_mod_idemp_r; last by rewrite /p -lock.
    f_equal ; ring.
  + (* Okayyyy So we cannot *create* y, thus we will have to redo it. *)
    have Eulers_Criterion2 := Eulers_criterion Zmodp.p Prime Prime2 (28948022309329048855892746252171976963317496166410141009864396001978282409975 *  (Zmodp.repr x)).
    rewrite /legendre in Eulers_Criterion2.
    destruct (ClassicalDescription.excluded_middle_informative _).
    * exfalso.
      clear Eulers_Criterion Eulers_Criterion2 n0 Prime2.
      rewrite modZp in n.
      have HP : 0 <= (Z.R x) < p by rewrite -modZp ; apply Z.mod_pos_bound ; rewrite /p -lock.
      move: n.
      have Hp : p <> 0 by rewrite /p -lock.
      have : Znumtheory.rel_prime p 28948022309329048855892746252171976963317496166410141009864396001978282409975.
        apply Znumtheory.rel_prime_sym.
        apply Znumtheory.rel_prime_le_prime => //=.
        by rewrite /p -lock.
      move: e.
      move/(Znumtheory.Zmod_divide (28948022309329048855892746252171976963317496166410141009864396001978282409975 * Z.R x) p Hp).
      move/Znumtheory.Gauss.
      move=> H/H.
      move/Znumtheory.Zdivide_bounds.
      move=> H'/H'.
      have ->: Z.abs p = p by rewrite /p -lock.
      have ->: Z.abs (Z.R x) = (Z.R x).
        rewrite Z.abs_eq_iff; omega.
      move => H''.
      omega.
    * destruct (ClassicalDescription.excluded_middle_informative _).
    clear Eulers_Criterion Eulers_Criterion2 n0 Prime2.
    move: e => [y Hy].
    exists (Zmodp.pi y).
    right.
    apply eq_inv_2.
    apply val_inj => /=.
    rewrite Z.mul_mod_idemp_l; last by rewrite /p -lock.
    rewrite Z.mul_mod_idemp_r; last by rewrite /p -lock.
    move: Hy.
    have ->: y^2 = y*y by ring.
    have ->: 28948022309329048855892746252171976963317496166410141009864396001978282409975 mod p = 28948022309329048855892746252171976963317496166410141009864396001978282409975 => //.
    by rewrite /p -lock.
    * exfalso.
      have Hp : p <> 0 by rewrite /p -lock.
      clear n0 n1 n2.
      move: Eulers_Criterion2.
      rewrite Z.pow_mul_l.
      rewrite -Zmult_mod_idemp_l.
      rewrite -Zmult_mod_idemp_r.
      rewrite -Eulers_Criterion.
      clear n Prime2 Prime Eulers_Criterion.
      have <-: -1 mod p = 28948022309329048855892746252171976963317496166410141009864396001978282409975 ^ ((p - 1) / 2) mod p.
      rewrite /p.
      have Hn : 0 < locked (2 ^ 255 - 19) by rewrite -lock.
      have := legendre_compute28948022309329048855892746252171976963317496166410141009864396001978282409975.
      have := Zpow_facts.Zpower_mod 28948022309329048855892746252171976963317496166410141009864396001978282409975 ((locked (2 ^ 255 - 19) - 1) / 2) (locked (2 ^ 255 - 19)) Hn.
      rewrite -lock.
      remember (28948022309329048855892746252171976963317496166410141009864396001978282409975 ^ ((2 ^ 255 - 19 - 1) / 2) mod (2 ^ 255 - 19)) as m.
      remember ((28948022309329048855892746252171976963317496166410141009864396001978282409975 mod (2 ^ 255 - 19)) ^ ((2 ^ 255 - 19 - 1) / 2) mod (2 ^ 255 - 19)) as m'.
      remember (-1 mod (2 ^ 255 - 19)) as m''.
      clear Heqm Heqm' Heqm''.
      move => -> -> //.
      rewrite /p -lock; compute ; congruence.
Qed.

Lemma x_is_on_curve_or_twist: forall x,
(*   (x != 0)%R -> *)
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

From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import curve25519_Fp2.

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
