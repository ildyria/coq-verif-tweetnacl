Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import prime_and_legendre Zmodp GRing_tools.
From Reciprocity Require Import Reciprocity.Reciprocity.
Import BinInt.

Require Import Ring.
Open Scope ring_scope.
Import GRing.Theory.

Local Lemma a_2_4 : (Zmodp.pi 486662) ^+ 2 - 4%:R = Zmodp.pi 236839902240.
Proof.
rewrite expr2 Zmodp_mulE /= Zmodp_oppE /= /Zmodp.p -lock /= Zmodp_addE //=.
Qed.

Lemma a_not_square (x : Zmodp.type) : x ^+ 2 != (Zmodp.pi 486662) ^+ 2 - 4%:R.
Proof.
rewrite a_2_4.
have Prime:(Znumtheory.prime Zmodp.p).
  rewrite /Zmodp.p -lock ; apply curve25519_numtheory_prime.
have Prime2:= ZmodP_mod2_eq_1.
replace (BinInt.Z.sub (BinInt.Z.pow 2 255) 19) with Zmodp.p in Prime2.
2: rewrite /Zmodp.p -lock //.
have Eulers_Criterion := Eulers_criterion Zmodp.p Prime Prime2 (Zmodp.repr (Zmodp.pi 236839902240)).
rewrite /legendre in Eulers_Criterion.
destruct (ClassicalDescription.excluded_middle_informative _).
- rename e into H.
  exfalso.
  move: H.
  rewrite piK /p -lock //.
- destruct (ClassicalDescription.excluded_middle_informative _).
  + rename e into H.
    exfalso.
    move: Eulers_Criterion.
    rewrite piK /p.
    2: rewrite -lock //.
    replace (236839902240 ^ ((locked (2 ^ 255 - 19)%Z - 1) / 2) mod locked (2 ^ 255 - 19)%Z)
    with ((-1) mod (2^255 - 19)) %Z.
    rewrite -lock //=.
    apply legendre_compute.
  + rename n0 into H.
    apply /negP => Hx.
    apply H.
    move: Hx.
    move /eqP => Hx.
    apply (f_equal (fun x => Zmodp.repr x)) in Hx.
    exists (Zmodp.repr x).
    move: Hx.
    rewrite expr2.
    rewrite Z.pow_2_r.
    rewrite modZp => <- //.
Qed.

Lemma two_not_square (x : Zmodp.type) : x ^+ 2 != 2%:R.
Proof.
have ->: 2%:R = Zmodp.pi 2.
rewrite /GRing.natmul /= /GRing.add /= /Zmodp.add ; f_equal ; rewrite piK /p -?lock //.
have Prime:(Znumtheory.prime Zmodp.p).
  rewrite /Zmodp.p -lock ; apply curve25519_numtheory_prime.
have Prime2:= ZmodP_mod2_eq_1.
replace (BinInt.Z.sub (BinInt.Z.pow 2 255) 19) with Zmodp.p in Prime2.
2: rewrite /Zmodp.p -lock //.
have Eulers_Criterion := Eulers_criterion Zmodp.p Prime Prime2 (Zmodp.repr (Zmodp.pi 2)).
rewrite /legendre in Eulers_Criterion.
destruct (ClassicalDescription.excluded_middle_informative _).
- rename e into H.
  exfalso.
  move: H.
  rewrite modZp piK /p -?lock //=.
- destruct (ClassicalDescription.excluded_middle_informative _).
  + rename e into H.
    exfalso.
    move: Eulers_Criterion.
    rewrite piK /p.
    2: rewrite -lock //.
    replace (2 ^ ((locked (2 ^ 255 - 19)%Z - 1) / 2) mod locked (2 ^ 255 - 19)%Z)
    with ((-1) mod (2^255 - 19)) %Z.
    rewrite -lock //=.
    apply legendre_compute2.
  + rename n0 into H.
    apply /negP => Hx.
    apply H.
    move: Hx.
    move /eqP => Hx.
    apply (f_equal (fun x => Zmodp.repr x)) in Hx.
    exists (Zmodp.repr x).
    move: Hx.
    rewrite expr2.
    rewrite Z.pow_2_r.
    rewrite modZp => <- //.
Qed.

Open Scope Z.

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
      have HP : 0 <= (Zmodp.repr x) < p by rewrite -modZp ; apply Z.mod_pos_bound ; rewrite /p -lock.
      move: n.
      have Hp : p <> 0 by rewrite /p -lock.
      have : Znumtheory.rel_prime p 28948022309329048855892746252171976963317496166410141009864396001978282409975.
        apply Znumtheory.rel_prime_sym.
        apply Znumtheory.rel_prime_le_prime => //=.
        by rewrite /p -lock.
      move: e.
      move/(Znumtheory.Zmod_divide (28948022309329048855892746252171976963317496166410141009864396001978282409975 * Zmodp.repr x) p Hp).
      move/Znumtheory.Gauss.
      move=> H/H.
      move/Znumtheory.Zdivide_bounds.
      move=> H'/H'.
      have ->: Z.abs p = p by rewrite /p -lock.
      have ->: Z.abs (Zmodp.repr x) = (Zmodp.repr x).
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

Close Scope Z.

Lemma forall_x_2_0_sqrt (x:Zmodp.type) : x ^+ 2 = 0 -> x = 0.
Proof.
  move/eqP.
  rewrite sqrf_eq0.
  move/eqP => -> //.
Qed.

Lemma x_y_dif_0 (x y:Zmodp.type) : x != 0 \/ y != 0 -> (x != 0 /\ y == 0) \/ (x == 0 /\ y != 0) \/ (x != 0 /\ y != 0).
Proof.
move/orP.
have := orNb (y == 0).
have := orNb (x == 0).
case (x == 0) ; case (y == 0) => //= => _ _ _ ; auto.
Qed.

Lemma x2_eq_2_y2 : forall (x y:Zmodp.type), x != 0 \/ y != 0 -> x ^+2 - 2%:R * y^+2 != 0.
Proof.
move => x y.
move/x_y_dif_0 => [|[]] [].
+ move/eqP => Hx /eqP => ->.
  ring_simplify_this; rewrite -expr2.
  by apply/eqP => Hx2 ; apply Hx; move/forall_x_2_0_sqrt:Hx2.
+ move/eqP => ->.
  ring_simplify_this; rewrite -expr2.
  move/eqP => Hy.
  apply/eqP => Hy2 ; apply Hy.
  move/eqP:Hy2.
  rewrite oppr_eq0.
  by move/eqP/time_2_eq_0/forall_x_2_0_sqrt.
+ move => Hx Hy.
apply/eqP.
move/GRing.subr0_eq.
move/(f_equal (fun t => t / (y^+2))).
have Hy2 : y^+2 != 0 by apply/eqP=> Hy2 ; move/eqP: Hy => Hy ; apply Hy; move/forall_x_2_0_sqrt:Hy2.
rewrite -(mulrA 2%:R) (mulfV Hy2).
have ->: 2%:R * 1 = 2%:R :> Zmodp.type by ring_simplify_this.
rewrite -exprVn.
rewrite -exprMn.
apply/eqP.
apply two_not_square.
Qed.

Close Scope ring_scope.
