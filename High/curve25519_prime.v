From Coqprime Require Import PocklingtonRefl.
From mathcomp Require Import ssreflect ssrbool prime.
From Tweetnacl.High Require Import curve25519_prime_cert prime_ssrprime.
Local Open Scope positive_scope.

Require Import Znat.

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

