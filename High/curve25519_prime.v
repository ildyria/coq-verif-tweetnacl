From Coqprime Require Import PocklingtonRefl.
From mathcomp Require Import ssreflect ssrbool prime.
From Tweetnacl.High Require Export curve25519_prime_cert prime_ssrprime.
Local Open Scope positive_scope.

Require Import Znat.
Require Import ZArith.Zpow_facts.

Lemma inj_pow : forall n m : nat, Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
Proof.
  intros. induction m.
  + reflexivity.
  + rewrite Nat.pow_succ_r; [|apply Nat.le_0_l].
    rewrite Nat2Z.inj_mul.
    rewrite IHm.
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r; [|apply Nat2Z.is_nonneg].
    reflexivity.
Qed.

Lemma Zof_nat_25519 : Z.of_nat (2^255 - 19) = 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z.
Proof.
  rewrite Nat2Z.inj_sub.
  + rewrite inj_pow. reflexivity.
  + assert (19 <= 2^5)%nat. apply Nat.leb_le. reflexivity.
    eapply Nat.le_trans. exact H.
    apply Nat.pow_le_mono_r. discriminate. apply Nat.leb_le. reflexivity.
Qed.

Lemma curve25519_prime : prime (2^255 - 19).
Proof. apply: prime_ssrprime ; rewrite Zof_nat_25519; exact: primo. Qed.

Lemma curve25519_numtheory_prime : Znumtheory.prime (2^255 - 19).
Proof. change (2^255 - 19)%Z with 57896044618658097711785492504343953926634992332820282019728792003956564819949%Z. exact: primo. Qed.

Lemma ZmodP_mod2_eq_1: BinInt.Z.modulo (2^255 - 19) 2 = 1%Z.
Proof. done. Qed.

Lemma legendre_compute: 
(-1 mod (2 ^ 255 - 19))%Z = 236839902240 ^ ((locked (2 ^ 255 - 19)%Z - 1) / 2) mod locked (2 ^ 255 - 19)%Z.
Proof.
rewrite -Zpow_mod_correct -lock ; vm_compute ; congruence.
Qed.

Lemma legendre_compute2:
(-1 mod (2 ^ 255 - 19))%Z = (2 mod (2 ^ 255 - 19)) ^ ((locked (2 ^ 255 - 19)%Z - 1) / 2) mod locked (2 ^ 255 - 19)%Z.
Proof.
rewrite -Zpow_mod_correct -lock ; vm_compute ; congruence.
Qed.

Lemma legendre_compute28948022309329048855892746252171976963317496166410141009864396001978282409975:
(-1 mod (2 ^ 255 - 19))%Z = (28948022309329048855892746252171976963317496166410141009864396001978282409975 mod (2 ^ 255 - 19)) ^ ((locked (2 ^ 255 - 19)%Z - 1) / 2) mod locked (2 ^ 255 - 19)%Z.
Proof.
rewrite -Zpow_mod_correct -lock ; vm_compute ; congruence.
Qed.
