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
