Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Mid.Reduce.

Module Mid.

Definition car25519 (n:ℤ) : ℤ  :=  38 * getCarry 256 n +  getResidue 256 n.

End Mid.

Notation ℤcar25519 := Mid.car25519.

Lemma Zcar25519_correct: forall n, n:𝓖𝓕 = (Mid.car25519 n) :𝓖𝓕.
Proof.
  intro n.
  unfold ℤcar25519.
  rewrite  <- Z.add_mod_idemp_l by (compute ; intro ; false).
  rewrite <- Zmult_mod_idemp_l.
  rewrite <- t2256is38.
  rewrite Zmult_mod_idemp_l.
  rewrite Z.add_mod_idemp_l.
  rewrite Z.add_comm.
  orewrite residuteCarry.
  compute ; intro ; false.
Qed.
