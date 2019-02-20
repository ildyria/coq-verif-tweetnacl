From Tweetnacl Require Import Libs.Export.
From Tweetnacl.High Require Import Zmodp opt_ladder curve25519 curve25519_prime prime_ssrprime.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg prime div.

From Tweetnacl Require Import Mod.

Open Scope Z.
(* Require Import Znat.
 *)

Lemma Z25519_is_prime: Znumtheory.prime (2 ^ 255 - 19).
Proof.
  have Hn: 1 < 2^255-19 => //.
  apply Znumtheory.prime_intro; auto with zarith.
  intros n (H,H'); Z.le_elim H; auto with zarith.
  1,2: apply Znumtheory.rel_prime_le_prime.
  2,4: omega.
  1,2: replace (2 ^ 255 - 19) with (Z.of_nat (2 ^ 255 - 19)).
  2,4:   rewrite Zof_nat_25519 ; reflexivity.
  1,2: apply ssrprime_prime.
  1,2: apply curve25519_prime.
Qed.

Lemma Inv25519_pow_mul x :
  Zmodp.repr x :𝓖𝓕 <> 0 ->
  Zmodp.repr x ^ (2 ^ 255 - 21) * Zmodp.repr x :𝓖𝓕 = 1.
Proof.
  move => Hx.
  have HP:= Z25519_is_prime.
  have HPnotNull : 2 ^ 255 - 19 <> 0 => //.
  have Hn: 1 < 2^255-19 => //.
  have Hp: Znumtheory.rel_prime (Zmodp.repr x) (2^255 -19).
    apply Znumtheory.rel_prime_le_prime => //.
  rewrite -modZp.
  rewrite /p -lock.
  have H25519 : 2 ^ 255 - 19 > 0.
    done.
  have HxP':= Z_mod_lt (Zmodp.repr x) (2 ^ 255 - 19) H25519.
  omega.
  have := Zp.phi_power_is_1 (Zmodp.repr x) (2 ^ 255 - 19) Hn Hp.
  rewrite Euler.prime_phi_n_minus_1 => //.
  change (2 ^ 255 - 19 - 1) with (1 + (2 ^ 255 - 21)).
  rewrite Zpower_exp => //.
  rewrite Z.pow_1_r.
  rewrite Z.mul_comm.
  done.
Qed.

Lemma fermat_eq_inverse x : modP (Zmodp.repr (Zmodp_inv x)) = modP ((Zmodp.repr x) ^ (2 ^ 255 - 21)).
Proof.
  have HP:= Z25519_is_prime.
  have HPnotNull : 2 ^ 255 - 19 <> 0.
    done.
  rewrite /Zmodp_inv.
  rewrite /modP /Zmodp_inv.
  elim (Zinv (Zmodp.repr x)).
  + by rewrite /p -lock pow_mod // => -> ; rewrite Z.pow_0_l //=.
  + rewrite /p -lock => Hx.
  have := Inv25519_pow_mul x Hx.
  remember (Zmodp.repr x) as P.
  remember (P ^ (2 ^ 255 - 21)) as Q.
  move => HPQ y.
  rewrite -HPQ.
  move/(f_equal (fun x => (x * Q) mod (2 ^ 255 - 19))).
  rewrite Z.mul_mod_idemp_l //.
  replace (y * P * Q) with (y * (P * Q)).
  2: ring.
  rewrite -Z.mul_mod_idemp_r // (Z.mul_comm P Q).
  rewrite HPQ Z.mul_1_r Z.mul_1_l.
  move=> ->.
  rewrite piK.
  rewrite Zmod_mod //.
  rewrite /p -lock.
  apply Zmodp.Z_mod_betweenb => //.
Qed.
