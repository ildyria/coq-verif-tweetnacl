From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Unpack25519.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import Inv25519.
From Tweetnacl.Low Require Import ScalarMult_rev.

From Tweetnacl.Low Require Import ScalarMult_rev_fn_gen.

From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl.Low Require Import Prep_n.
From Tweetnacl.Low Require Import GetBit.
From Tweetnacl.Mid Require Import Unpack25519.
From Tweetnacl.Mid Require Import Pack25519.
From Tweetnacl.Mid Require Import Inv25519.
From Tweetnacl.Mid Require Import ScalarMult_rev.
From Tweetnacl.Mid Require Import Prep_n.
From Tweetnacl.Mid Require Import GetBit.
From Tweetnacl.Mid Require Import Crypto_Scalarmult.

From Tweetnacl.Mid Require Import ScalarMult_rev_fn_gen.

Open Scope Z.

Definition Crypto_Scalarmult n p :=
  let a := get_a (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  let c := get_c (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  Pack25519 (M a (Inv25519 c)).

Lemma impl_omega_simpl_0 : ∀ x : ℤ, (λ x0 : ℤ, 0 ≤ x0 ∧ x0 < 2 ^ 16) x → -38 ≤ x ∧ x < 2 ^ 16 + 38.
Proof.
  intros ; simpl in *.
  change (2^16 + 38) with 65574.
  change (2^16) with 65536 in H.
  omega.
Qed.

Lemma impl_omega_simpl_1 : ∀ x : ℤ, (λ x0 : ℤ, -38 ≤ x0 ∧ x0 < 2 ^ 16 + 38) x → - 2 ^ 26 < x ∧ x < 2 ^ 26.
Proof.
  intros ; simpl in *.
  change (2^16 + 38) with 65574 in H.
  change (2^26) with 67108864.
  omega.
Qed.

Lemma impl_omega_simpl_2 : ∀ x : ℤ, (λ x0 : ℤ, -38 ≤ x0 ∧ x0 < 2 ^ 16 + 38) x → - 2 ^ 62 < x ∧ x < 2 ^ 62.
Proof.
  intros ; simpl in *.
  change (2^16 + 38) with 65574 in H.
  change (2^62) with 4611686018427387904.
  omega.
Qed.

Theorem Crypto_Scalarmult_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = ZCrypto_Scalarmult (ZofList 8 n) (ZofList 8 p).
Proof.
  intros n p Hln Hlp Hbn Hbp.
  rewrite /Crypto_Scalarmult /ZCrypto_Scalarmult.
  assert(Zlength One16 = 16) by go.
  assert(Zlength nul16 = 16) by go.
  assert(Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) One16) by
    (repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go).
  assert(Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) nul16) by
    (repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go).
  assert(Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 16) (Unpack25519 p)).
    apply Unpack25519_bounded.
    assumption.
  assert(Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p)).
    eapply list.Forall_impl.
    eassumption.
    apply impl_omega_simpl_0.
  assert(Zlength (Unpack25519 p) = 16).
    apply Unpack25519_Zlength.
    assumption.
  assert(Zlength (Unpack25519 n) = 16).
    apply Unpack25519_Zlength.
    assumption.
  assert(Zlength (get_a (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) =
16).
  {
  apply get_a_montgomery_fn_Zlength.
  3,8: apply Unpack25519_Zlength.
  all: try omega ; try assumption.
  }
  assert(Zlength (get_c (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) =
16).
  {
  apply get_c_montgomery_fn_Zlength.
  3,8: apply Unpack25519_Zlength.
  all: try omega ; try assumption.
  }
  rewrite Pack25519_mod_25519.
  2: {
  apply M_Zlength.
  2: apply Inv25519_Zlength.
  all: assumption.
  }
  2: {
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  5: apply impl_omega_simpl_2.
  2: apply Inv25519_Zlength.
  1,2: assumption.
  eapply list.Forall_impl.
  apply get_a_montgomery_fn_bound.
  all: try assumption.
  omega.
  apply impl_omega_simpl_1.
  eapply list.Forall_impl.
  apply Inv25519_bound_Zlength.
  assumption.
  apply get_c_montgomery_fn_bound.
  all: try assumption.
  omega.
  apply impl_omega_simpl_1.
  }
  rewrite /ZPack25519.
  rewrite mult_GF_Zlengh.
  3: apply Inv25519_Zlength.
  2,3: assumption.
  rewrite -Zmult_mod_idemp_l.
  rewrite -Zmult_mod_idemp_r.
  symmetry.
  rewrite -Zmult_mod_idemp_l.
  rewrite -Zmult_mod_idemp_r.
  f_equal.
  f_equal.
  unfold Zmontgomery_fn.
  unfold montgomery_fn.

  admit.
  rewrite Inv25519_Z_GF.
  2: assumption.
  rewrite Inv25519_Z_correct /ZInv25519.
  rewrite pow_mod.
  symmetry.
  rewrite pow_mod.
  2,3: compute; discriminate.
  f_equal.
  f_equal.
  admit.
Admitted.




