Set Warnings "-notation-overridden,-parsing".
Require Import ZArith Znumtheory Znat.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat div prime.

Theorem prime_ssrprime (n : nat) : Znumtheory.prime (Z.of_nat n) -> prime n.
Proof.
  move=> [n_geq1 Hrel_prime].
  apply/primeP.
  split; first by apply/ltP/Nat2Z.inj_lt; apply: n_geq1.
  move=> d d_divn.
  apply: contraT; rewrite negb_or => /andP [d_neq1 d_neqn].
  have /andP [one_ltd d_ltn] : (1 < d < n)%N.
    have zero_leqn : (0 < n)%N.
      apply/ltP/Nat2Z.inj_lt.
      apply: Z.lt_succ_l.
      by apply: n_geq1.
    have zero_leqd : (0 < d)%N by apply: dvdn_gt0; last by apply: d_divn.
    rewrite ltn_neqAle eq_sym d_neq1 zero_leqd.
    rewrite ltn_neqAle d_neqn.
    by apply: dvdn_leq.
  have [_ _ Hgcd] : rel_prime (Z.of_nat d) (Z.of_nat n).
    apply: Hrel_prime.
    split; last by apply/Nat2Z.inj_lt/ltP.
    rewrite -/(Z.of_nat 1).
    apply/Nat2Z.inj_le/leP.
    apply: ltn_trans; last by apply: one_ltd.
    by apply: ltnSn.
  have : d == 1%N.
    apply/eqP/Nat2Z.inj.
    apply: Z.divide_1_r_nonneg; first by apply: Nat2Z.is_nonneg.
    apply: Hgcd; first by apply: Z.divide_refl.
    exists (Z.of_nat (n %/ d)).
    by rewrite -Nat2Z.inj_mul multE divnK.
  by rewrite (negbTE d_neq1).
Qed.

Theorem ssrprime_prime (p : nat) : prime p -> Znumtheory.prime (Z.of_nat p).
Proof.
  have Hp': exists p', p' = Z.of_nat p /\ p = Z.to_nat p'.
  eexists ; split ; try reflexivity.
  symmetry ; apply Nat2Z.id.
  move: Hp'.
  rename p into p'.
  move => [p []] <- ->.

  move /primeP => [] Hp Hprime.
  apply prime_intro.
  + have : p < 0 \/ p = 0 \/ p = 1 \/ 1 < p.
      by omega.
    move=> [H|[H|[H|H]]] ; try omega ; move: Hp.
    + move: H ; elim p => //.
    + move: H -> => //=.
    + move: H -> => //=.
  + move => n Hn.
    have Hpp: 0 < p.
      omega.
    have Hppp: 0 <= p.
      omega.
    rewrite /rel_prime.
    apply Zis_gcd_intro; try apply Z.divide_1_l.
    move => x Hxn Hxp.
    apply Zdivide_Zabs_inv_l in Hxp.
    destruct Hxp.
    have Hxx0: 0 < x0 * Z.abs x.
      omega.
    have Hx:= (Z.abs_nonneg x).
    have H1: 0 <= 1.
      omega.
    have Hxx: 0 < Z.abs x.
      apply Z.lt_0_mul in Hxx0.
      move: Hxx0 => [[_ ]|[Hc _]] //.
      omega.
    have Hx0: 0 < x0.
      eapply Zmult_lt_0_reg_r.
      2: eassumption.
      done.
    have : exists k : nat, Z.to_nat p = (k * (Z.to_nat (Z.abs x)))%N.
    move: H ; rewrite -Z2Nat.inj_iff; try omega.
    move => ->.
    rewrite Z2Nat.inj_mul ; try omega.
    exists (Z.to_nat x0).
    reflexivity.
    move/dvdnP /Hprime /orP => [] /eqP.
    change 1%N with (Z.to_nat 1).
    all: rewrite Z2Nat.inj_iff //.
    + have := Zabs_dec x.
      move=> [].
      move => <- ->.
      apply Z.divide_refl.
      move => Hxxx.
      have ->: (Z.abs x = - x).
        omega.
      move => Hxxxx.
      apply Zdivide_opp_l_rev.
      rewrite Hxxxx.
      apply Z.divide_refl.
    + move => XP.
      exfalso.
      have := Zabs_dec x.
      move=> [] => Hxs.
      1: rewrite -Hxs in XP ; subst x.
      2: rewrite XP in Hxs ; subst x ; apply Zdivide_opp_l_rev in Hxn.
      all: clear x0 H Hx0 Hxx0 Hx Hxx Hprime Hp.
      all: move: Hxn.
      all: rewrite /Z.divide.
      all: move => [x] Hxnp.
      all: have Hxnp':= Hxnp.
      all: move: Hxnp'.
      all: replace (x * p) with (x * p + 0).
      2,4: omega.
      all: rewrite Z.mul_comm.
      all: have Hpppp: 0 <= 0 < p.
      1,3: omega.
      all: move /(Zdiv_unique _ _ _ _ Hpppp).
      all: move => Hx; symmetry in Hx.
      all: move: Hx.
      all: rewrite Zdiv_small.
      2,4: omega.
      all: move => Hx ; subst x.
      all: rewrite Z.mul_0_l in Hxnp ; omega.
Qed.
