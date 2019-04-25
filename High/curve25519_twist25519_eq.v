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

