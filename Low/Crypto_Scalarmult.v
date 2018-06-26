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
(* From Tweetnacl.Low Require Import A. *)
(* From Tweetnacl.Low Require Import Z. *)
From Tweetnacl.Low Require Import M.
(* From Tweetnacl.Low Require Import S. *)
From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Unpack25519.
From Tweetnacl.Low Require Import Inv25519.
From Tweetnacl.Low Require Import ScalarMult_rev.
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

Section Crypto_Scalarmult.

Definition Mod := (fun x => Z.modulo x (Z.pow 2 255 - 19)).
Context (Z_Ops            : (Ops Z Z) Mod).
Context (List_Z_Ops       : Ops (list Z) (list Z) id).
Context (List_Z_Ops_Prop          : @Ops_List List_Z_Ops).
Context (List_Z_Ops_Prop_Correct  : @Ops_Prop_List_Z Mod List_Z_Ops Z_Ops).
Local Instance List16_Ops         : (Ops (@List16 Z) (List32B) id) := {}.
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
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.
Local Instance List16_Z_Eq      : @Ops_Mod_P (@List16 Z) (List32B) Z Mod id List16_Ops Z_Ops := {
P l := (ZofList 16 (List16_to_List l));
P' l := (ZofList 8 (List32_to_List l));
}.
Proof.
- intros [a Ha] [b Hb] ; simpl List16_to_List; rewrite -A_correct; reflexivity.
- intros [a Ha] [b Hb] ; simpl List16_to_List.
  apply AMZubSqSel_Correct.mult_GF_Zlengh ; assumption.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; rewrite -Zub_correct; reflexivity.
- intros [a Ha] ; simpl List16_to_List ; apply Sq_GF_Zlengh ; try assumption.
- simpl List16_to_List ; f_equal; rewrite -C_121665_correct ; reflexivity.
- simpl List16_to_List ; f_equal; rewrite -C_0_correct ; reflexivity.
- simpl List16_to_List ; f_equal; rewrite -C_1_correct ; reflexivity.
- intros b [p Hp] [q Hq] ; simpl List16_to_List ; f_equal ; rewrite -Sel25519_correct ; reflexivity.
- intros b [p Hp] ; simpl ; symmetry ; rewrite GetBit_correct ; try assumption ; reflexivity.
Defined.
Local Instance List16_List_Z_Eq : @Ops_Mod_P (List16 Z) (List32B) (list Z) id id List16_Ops List_Z_Ops := {
P := List16_to_List;
P' := List32_to_List
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

Definition Crypto_Scalarmult n p :=
  let a := get_a (montgomery_fn List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  let c := get_c (montgomery_fn List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
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

Local Lemma Zlength_a : forall n p,
  Zlength n = 32 ->
  Zlength p = 32 ->
Zlength (get_a (montgomery_fn List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) = 16.
Proof.
  intros.
  apply get_a_montgomery_fn_Zlength.
  eassumption.
  3,8: apply Unpack25519_Zlength.
  all: try omega ; try assumption.
  all : go.
Qed.

Local Lemma Zlength_c : forall n p,
  Zlength n = 32 ->
  Zlength p = 32 ->
Zlength (get_c (montgomery_fn List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) = 16.
Proof.
  intros.
  apply get_c_montgomery_fn_Zlength.
  eassumption.
  3,8: apply Unpack25519_Zlength.
  all: try omega ; try assumption.
  all : go.
Qed.

Local Lemma One_bound_ext: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) One16.
Proof.
repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go.
Qed.
Local Lemma nul_bound_ext: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) nul16.
Proof.
repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go.
Qed.

Local Lemma M_bounded :  forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
Forall (λ x : ℤ, - 2 ^ 62 < x ∧ x < 2 ^ 62)
  (M.M
     (get_a
        (montgomery_fn List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)))
     (Inv25519
        (get_c
           (montgomery_fn List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16
              (Unpack25519 p))))).
Proof.
  intros n p Hln Hlp Hbn Hbp.
  assert(HUnpack:= Unpack25519_bounded p Hbp).
  assert(HUnpackEx: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p)).
    eapply list.Forall_impl.
    eassumption.
    apply impl_omega_simpl_0.
  assert(HlUnpackP: Zlength (Unpack25519 p) = 16).
    apply Unpack25519_Zlength.
    assumption.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  5: apply impl_omega_simpl_2.
  2: apply Inv25519_Zlength.
  2: apply Zlength_c ; assumption.
  1: apply Zlength_a ; assumption.
  eapply list.Forall_impl.
  apply get_a_montgomery_fn_bound.
  all: try assumption.
  omega.
  all: try apply Zlength_One16.
  all: try apply nul_bound_ext.
  all: try apply One_bound_ext.
  apply impl_omega_simpl_1.
  eapply list.Forall_impl.
  apply Inv25519_bound_Zlength.
  apply Zlength_c ; assumption.
  apply get_c_montgomery_fn_bound.
  all: try assumption.
  omega.
  all: try apply Zlength_One16.
  all: try apply nul_bound_ext.
  all: try apply One_bound_ext.
  apply impl_omega_simpl_1.
Qed.

Theorem Crypto_Scalarmult_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = ZCrypto_Scalarmult_rev_gen Z_Ops (ZofList 8 n) (ZofList 8 p).
Proof.
  intros n p Hln Hlp Hbn Hbp.
  rewrite /Crypto_Scalarmult /ZCrypto_Scalarmult_rev_gen.
  assert(HUnpack:= Unpack25519_bounded p Hbp).
  assert(HCn:= clamp_bound n Hbn).
  assert(HUnpackEx: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p)).
    eapply list.Forall_impl ; [eassumption | apply impl_omega_simpl_0].
  assert(HlUnpackP: Zlength (Unpack25519 p) = 16).
    apply Unpack25519_Zlength ; assumption.
  rewrite Pack25519_mod_25519.
  2: {
  apply M_Zlength.
  2: apply Inv25519_Zlength.
  2: apply Zlength_c ; assumption.
  1: apply Zlength_a ; assumption.
  }
  2: apply M_bounded ; assumption.
  rewrite /ZPack25519.
  rewrite mult_GF_Zlengh.
  3: apply Inv25519_Zlength.
  2: apply Zlength_a ; assumption.
  2: apply Zlength_c ; assumption.
  rewrite -Zmult_mod_idemp_l.
  rewrite -Zmult_mod_idemp_r.
  symmetry.
  rewrite -Zmult_mod_idemp_l.
  rewrite -Zmult_mod_idemp_r.
  f_equal.
  f_equal.
  symmetry.
  2: rewrite Inv25519_Z_GF.
  3: apply Zlength_c ; assumption.
  2: rewrite Inv25519_Z_correct /ZInv25519.
  2: rewrite pow_mod.
  2: symmetry.
  2: rewrite pow_mod.
  3,4: compute; discriminate.
  2: f_equal ; f_equal.
  1,2: rewrite /Zmontgomery_fn /montgomery_fn.
  1,2: assert(H255: 0 <= 255) by omega.
  1,2: rewrite clamp_ZofList_eq ?Unpack25519_eq_ZUnpack25519.
  apply (abstract_fn_rev_eq_List_Z_a (fun x => Z.modulo x (Z.pow 2 255 - 19)) Z_Ops List_Z_Ops List_Z_Ops_Prop List_Z_Ops_Prop_Correct).
  8: apply (abstract_fn_rev_eq_List_Z_c (fun x => Z.modulo x (Z.pow 2 255 - 19)) Z_Ops List_Z_Ops List_Z_Ops_Prop List_Z_Ops_Prop_Correct).
  all: try assumption.
  all: rewrite Zlength_correct in Hln.
  all: rewrite Zlength_correct in Hlp.
  all: try omega.
Qed.

End Crypto_Scalarmult.


Close Scope Z.