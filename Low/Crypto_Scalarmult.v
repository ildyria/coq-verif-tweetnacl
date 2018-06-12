From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Low Require Import AMZubSqSel_Correct.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import AMZubSqSel_List.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.
From Tweetnacl.Low Require Import A.
From Tweetnacl.Low Require Import Z.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import S.
From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Unpack25519.
From Tweetnacl.Low Require Import Inv25519.
From Tweetnacl.Low Require Import ScalarMult_rev.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl.Low Require Import Prep_n.
From Tweetnacl.Low Require Import GetBit.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import List16.
From Tweetnacl.Low Require Import ScalarMult_gen_small.
From Tweetnacl.Mid Require Import Unpack25519.
From Tweetnacl.Mid Require Import Pack25519.
From Tweetnacl.Mid Require Import Inv25519.
From Tweetnacl.Mid Require Import Prep_n.
From Tweetnacl.Mid Require Import GetBit.
From Tweetnacl.Mid Require Import Crypto_Scalarmult.
From Tweetnacl.Mid Require Import AMZubSqSel.
From Tweetnacl.Mid Require Import ScalarMult.
From Tweetnacl.Low Require Import Crypto_Scalarmult_lemmas.

Open Scope Z.

Local Instance Z_Ops : (Ops Z Z) := {}.
Proof.
apply A.
apply M.
apply Zub.
apply Sq.
apply C_0.
apply C_1.
apply C_121665.
apply Sel25519.
apply Zgetbit.
apply (fun x => Z.modulo x ((Z.pow 2 255) - 19)).
intros b p q ; rewrite /Sel25519 ; flatten.
intros ; apply A_mod_eq.
intros ; apply M_mod_eq.
intros ; apply Zub_mod_eq.
intros ; apply Sq_mod_eq.
intros ; apply Zmod_mod.
Defined.

Local Instance List_Z_Ops : Ops (list Z) (list Z) := {}.
Proof.
apply A.A.
apply M.M.
apply Z.Zub.
apply S.Sq.
apply nul16.
apply One16.
apply Constant.c_121665.
apply Sel25519.Sel25519.
apply GetBit.getbit.
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.

Local Instance List_Z_Ops_Prop : (@Ops_List List_Z_Ops) :=  {}.
Proof.
apply A.A_Zlength.
apply M.M_Zlength.
apply Z.Zub_Zlength.
apply S.Sq_Zlength.
apply Sel25519.Sel25519_Zlength.
apply Constant.Zlength_c_121665.
apply Constant.Zlength_c_121665.
apply Constant.Zlength_c_121665.
apply M.M_bound_Zlength.
apply S.Sq_bound_Zlength.
apply A.A_bound_Zlength_le.
apply A.A_bound_Zlength_lt.
apply Z.Zub_bound_Zlength_le.
apply Z.Zub_bound_Zlength_lt.
apply Sel25519.Sel25519_bound_le.
apply Sel25519.Sel25519_bound_lt_trans_le.
apply Sel25519.Sel25519_bound_lt.
apply Sel25519.Sel25519_bound_lt_le_id.
apply Sel25519.Sel25519_bound_lt_lt_id.
apply Sel25519.Sel25519_bound_le_le_id.
apply Sel25519.Sel25519_bound_le_lt_trans_le_id.
apply C_121665_bounds.
apply nul16_bounds.
apply One16_bounds.
Defined.

Local Instance List_Z_Ops_Prop_Correct  : @Ops_Prop_List_Z List_Z_Ops Z_Ops := {}.
Proof.
apply A_correct.
intros; simpl.
rewrite mult_GF_Zlengh.
rewrite /M.
rewrite -?Car25519.Zcar25519_correct.
reflexivity.
assumption.
assumption.
apply Zub_correct.
intros. simpl.
rewrite /Sq.
rewrite mult_GF_Zlengh.
rewrite /M.
rewrite -?Car25519.Zcar25519_correct.
reflexivity.
assumption.
assumption.
reflexivity.
reflexivity.
reflexivity.
intros; simpl.
rewrite /Sel25519 /Sel25519.Sel25519 /Sel25519.list_cswap ; flatten.
intros. simpl.
apply getbit_repr.
assumption.
Qed.

Local Instance List16_Ops : (Ops (@List16 Z) (List32B)) := {}.
Proof.
apply A_List16.
apply M_List16.
apply Zub_List16.
apply Sq_List16.
apply C_0_List16.
apply C_1_List16.
apply C_121665_List16.
apply Sel25519_List16.
apply getbit_List32B.
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.

Local Instance List16_List_Z_Eq : @Ops_Mod_P (List16 Z) (List32B) (list Z) List16_Ops List_Z_Ops := {
P := List16_to_List;
P' := List32_to_List;
}.
Proof.
intros [] [] ; reflexivity.
intros [] [] ; reflexivity.
intros [] [] ; reflexivity.
intros [] ; reflexivity.
reflexivity.
reflexivity.
reflexivity.
intros b [] [] ; reflexivity.
intros i [] ; reflexivity.
Defined.

Local Instance List16_Z_Eq : @Ops_Mod_P (@List16 Z) (List32B) Z List16_Ops Z_Ops := {
P l := (ZofList 16 (List16_to_List l));
P' l := (ZofList 8 (List32_to_List l));
}.
Proof.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; apply A_correct.
- intros [a Ha] [b Hb] ; simpl List16_to_List;
rewrite /Mod /M /Z_Ops /AMZubSqSel.M.
rewrite -?Car25519.Zcar25519_correct;
apply mult_GF_Zlengh ; assumption.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; apply Zub_correct.
- intros [a Ha] ; simpl List16_to_List;
rewrite /Mod /S.Sq /Sq /Z_Ops /AMZubSqSel.Sq /AMZubSqSel.M;
rewrite -?Car25519.Zcar25519_correct;
apply mult_GF_Zlengh ; assumption.
- reflexivity.
- reflexivity.
- reflexivity.
- intros b [p Hp] [q Hq] ; simpl List16_to_List ;
rewrite /Sel25519.Sel25519 /Sel25519.list_cswap /Gen.AMZubSqSel.Sel25519 /Z_Ops /Sel25519;
rewrite /Sel25519.list_cswap; flatten.
intros b [p Hp] ; simpl ; symmetry; apply getbit_repr; assumption.
Defined.

Definition Crypto_Scalarmult n p :=
  let a := get_a (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  let c := get_c (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  Pack25519 (M.M a (Inv25519 c)).

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
  rewrite ZCrypto_Scalarmult_eq.
  rewrite /Crypto_Scalarmult /ZCrypto_Scalarmult_rev_gen.
  assert(HlOne16: Zlength One16 = 16) by go.
  assert(HlNul16: Zlength nul16 = 16) by go.
  assert(HbOne16: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) One16) by
    (repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go).
  assert(HbNul16: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) nul16) by
    (repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go).
  assert(HUnpack: Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 16) (Unpack25519 p)).
    apply Unpack25519_bounded.
    assumption.
  assert(HCn:= clamp_bound n Hbn).
  assert(HUnpackEx: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p)).
    eapply list.Forall_impl.
    eassumption.
    apply impl_omega_simpl_0.
  assert(HlUnpackP: Zlength (Unpack25519 p) = 16).
    apply Unpack25519_Zlength.
    assumption.
  assert(HlgetA: Zlength (get_a (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) =
16).
  {
  apply get_a_montgomery_fn_Zlength.
  3,8: apply Unpack25519_Zlength.
  all: try omega ; try assumption.
  }
  assert(HlgetC: Zlength (get_c (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) =
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
  symmetry.
  2: rewrite Inv25519_Z_GF.
  3: assumption.
  2: rewrite Inv25519_Z_correct /ZInv25519.
  2: rewrite pow_mod.
  2: symmetry.
  2: rewrite pow_mod.
  3,4: compute; discriminate.
  2: f_equal ; f_equal.
  1,2: rewrite /Zmontgomery_fn /montgomery_fn.

  1,2: assert(H255: 0 <= 255) by omega.
  pose (HOpsL := AMZubSqSel_Correct.Ops_Prop_List_Z).
  1: assert(Equiv := abstract_fn_rev_eq_List_Z_a Z_Ops List_Z_Ops_Prop List_Z_Ops_Prop_Correct 255 254 (clamp n) (Unpack25519 p) H255 HlUnpackP HCn).
  2: assert(Equiv := abstract_fn_rev_eq_List_Z_c Z_Ops List_Z_Ops_Prop List_Z_Ops_Prop_Correct 255 254 (clamp n) (Unpack25519 p) H255 HlUnpackP HCn).
  1,2: rewrite /Mod /Z_Ops in Equiv.
  1,2: rewrite Equiv.
  1,2: f_equal ; f_equal ; f_equal.
  1,4: symmetry ; apply clamp_ZofList_eq.
  5,6,7,8: symmetry ; apply Unpack25519_eq_ZUnpack25519.
  all: try assumption.
  all: rewrite Zlength_correct in Hln.
  all: rewrite Zlength_correct in Hlp ; omega.
Qed.


Close Scope Z.