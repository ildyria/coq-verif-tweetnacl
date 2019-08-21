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
From Tweetnacl.Gen Require Import montgomery_rec.
From Tweetnacl.Gen Require Import montgomery_rec_eq.
From Tweetnacl.Low Require Import M.
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
From Tweetnacl.Low Require Import Crypto_Scalarmult_lemmas.
From Tweetnacl.Mid Require Import Mod.
From Tweetnacl.Mid Require Import Instances.

Open Scope Z.

(* Real version for proof *)
Definition Crypto_Scalarmult_proof n p :=
  let a := get_a (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p)) in
  let c := get_c (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p)) in
  Pack25519 (Low.M a (Inv25519 c)).

(* Pretty version for Paper *)
Definition Crypto_Scalarmult n p :=
  let a := get_a (montgomery_rec 255 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p)) in
  let c := get_c (montgomery_rec 255 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p)) in
  Pack25519 (Low.M a (Inv25519 c)).

(* Proof of equivalence between the two *)
Lemma Crypto_Scalarmult_eq : forall n p, 
  Crypto_Scalarmult_proof n p = Crypto_Scalarmult n p.
Proof.
  move => n p.
  rewrite /Crypto_Scalarmult_proof /Crypto_Scalarmult.
  apply f_equal.
  apply f_equal2.
  2: apply f_equal.
  all: apply f_equal.
  all: rewrite /montgomery_fn.
  all: change 255 with (254+1).
  all: rewrite -montgomery_rec_eq_fn_rev ; f_equal; omega.
Qed.

Local Lemma impl_omega_simpl_0 : ∀ x : ℤ, (λ x0 : ℤ, 0 ≤ x0 ∧ x0 < 2 ^ 16) x → -38 ≤ x ∧ x < 2 ^ 16 + 38.
Proof.
  intros ; simpl in *.
  change (2^16 + 38) with 65574.
  change (2^16) with 65536 in H.
  omega.
Qed.

Local Lemma impl_omega_simpl_1 : ∀ x : ℤ, (λ x0 : ℤ, -38 ≤ x0 ∧ x0 < 2 ^ 16 + 38) x → - 2 ^ 26 < x ∧ x < 2 ^ 26.
Proof.
  intros ; simpl in *.
  change (2^16 + 38) with 65574 in H.
  change (2^26) with 67108864.
  omega.
Qed.

Local Lemma impl_omega_simpl_2 : ∀ x : ℤ, (λ x0 : ℤ, -38 ≤ x0 ∧ x0 < 2 ^ 16 + 38) x → - 2 ^ 62 < x ∧ x < 2 ^ 62.
Proof.
  intros ; simpl in *.
  change (2^16 + 38) with 65574 in H.
  change (2^62) with 4611686018427387904.
  omega.
Qed.

Local Lemma Zlength_a : forall n p,
  Zlength n = 32 ->
  Zlength p = 32 ->
Zlength (get_a (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p))) = 16.
Proof.
  intros.
  apply get_a_montgomery_fn_Zlength => //.
  apply List_Z_Ops_Prop.
  all: apply Unpack25519_Zlength => //.
Qed.

Local Lemma Zlength_c : forall n p,
  Zlength n = 32 ->
  Zlength p = 32 ->
Zlength (get_c (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p))) = 16.
Proof.
  intros.
  apply get_c_montgomery_fn_Zlength => //.
  apply List_Z_Ops_Prop.
  all: apply Unpack25519_Zlength => //.
Qed.

Local Lemma C_1_bound_ext: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) Low.C_1.
Proof.
repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go.
Qed.
Local Lemma C_0_bound_ext: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) Low.C_0.
Proof.
repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go.
Qed.

Local Lemma M_bounded :  forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
Forall (λ x : ℤ, - 2 ^ 62 < x ∧ x < 2 ^ 62)
  (Low.M
     (get_a
        (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0 (Unpack25519 p)))
     (Inv25519
        (get_c
           (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0
              (Unpack25519 p))))).
Proof.
  intros n p Hln Hlp Hbn Hbp.
  have HUnpack:= Unpack25519_bounded p Hbp.
  have HUnpackEx: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p).
    eapply list.Forall_impl => //.
    eassumption.
    apply impl_omega_simpl_0.
  have HlUnpackP: Zlength (Unpack25519 p) = 16.
    apply Unpack25519_Zlength => //.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  5: apply impl_omega_simpl_2.
  2: apply Inv25519_Zlength.
  2: apply Zlength_c => //.
  1: apply Zlength_a => //.
  all: eapply list.Forall_impl.
  3: apply Inv25519_bound_Zlength.
  3: apply Zlength_c => //.
  3: apply get_c_montgomery_fn_bound => //.
  apply get_a_montgomery_fn_bound => //.
  1, 6: apply List_Z_Ops_Prop.
  all: try apply C_0_bound_ext.
  all: try apply C_1_bound_ext.
  all: apply impl_omega_simpl_1.
Qed.

Local Lemma get_a_abstract_fn_montgomery_fn n p:
Zlength n = 32 ->
Zlength p = 32 ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 16) (Unpack25519 p) ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) (clamp n) ->
Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p) ->
Zlength (Unpack25519 p) = 16 ->
get_a
  (abstract_fn_rev 255 254 (Zclamp (ZofList 8 n)) 1 (ZUnpack25519 (ZofList 8 p)) 0 1 0 0
     (ZUnpack25519 (ZofList 8 p))) `mod` (2 ^ 255 - 19) =
(ℤ16.lst get_a
           (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0 Low.C_0
              (Unpack25519 p))) `mod` (2 ^ 255 - 19).
Proof.
move => Hln Hlp Hbn Hbp HUnpack HCn HUnpackEx HlUnpackP.
rewrite /montgomery_fn.
have H255: 0 <= 255 by omega.
rewrite Zlength_correct in Hln.
rewrite Zlength_correct in Hlp.
rewrite clamp_ZofList_eq ?Unpack25519_eq_ZUnpack25519 => // ; try omega.
symmetry.
apply (abstract_fn_rev_eq_List_Z_a (fun x => Z.modulo x (Z.pow 2 255 - 19)) Z_Ops List_Z_Ops List_Z_Ops_Prop List_Z_Ops_Prop_Correct) => //.
Qed.

Local Lemma get_c_abstract_fn_montgomery_fn n p:
Zlength n = 32 ->
Zlength p = 32 ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 16) (Unpack25519 p) ->
Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) (clamp n) ->
Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p) ->
Zlength (Unpack25519 p) = 16 ->
ZInv25519
  (get_c
     (abstract_fn_rev 255 254 (Zclamp (ZofList 8 n)) 1 (ZUnpack25519 (ZofList 8 p)) 0 1 0 0
        (ZUnpack25519 (ZofList 8 p)))) `mod` (2 ^ 255 - 19) =
(ℤ16.lst Inv25519
           (get_c
              (montgomery_fn List_Z_Ops 255 254 (clamp n) Low.C_1 (Unpack25519 p) Low.C_0 Low.C_1 Low.C_0
                 Low.C_0 (Unpack25519 p)))) `mod` (2 ^ 255 - 19).
Proof.
move => Hln Hlp Hbn Hbp HUnpack HCn HUnpackEx HlUnpackP.
rewrite Inv25519_Z_GF.
2: by apply Zlength_c.
rewrite Inv25519_Z_correct /ZInv25519 pow_mod.
symmetry.
rewrite pow_mod.
2,3: by compute.
f_equal ; f_equal.
have H255: 0 <= 255 by omega.
rewrite Zlength_correct in Hln.
rewrite Zlength_correct in Hlp.
rewrite /montgomery_fn clamp_ZofList_eq ?Unpack25519_eq_ZUnpack25519 => // ; try omega.
apply (abstract_fn_rev_eq_List_Z_c (fun x => Z.modulo x (Z.pow 2 255 - 19)) Z_Ops List_Z_Ops List_Z_Ops_Prop List_Z_Ops_Prop_Correct) => //.
Qed.

Theorem Crypto_Scalarmult_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = ZCrypto_Scalarmult (ZofList 8 n) (ZofList 8 p).
Proof.
  intros n p Hln Hlp Hbn Hbp.
  rewrite -Crypto_Scalarmult_eq.
  rewrite /Crypto_Scalarmult_proof ZCrypto_Scalarmult_eq /ZCrypto_Scalarmult_rev_gen.
  have HUnpack:= Unpack25519_bounded p Hbp.
  have HCn:= clamp_bound n Hbn.
  have HUnpackEx: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p)
    by eapply list.Forall_impl ; [eassumption | apply impl_omega_simpl_0].
  have HlUnpackP: Zlength (Unpack25519 p) = 16
    by apply Unpack25519_Zlength.
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
  Opaque abstract_fn_rev.
  Opaque montgomery_fn.
  f_equal.
  f_equal.
  apply get_a_abstract_fn_montgomery_fn => //.
  apply get_c_abstract_fn_montgomery_fn => //.
Qed.

Corollary Crypto_Scalarmult_Eq2 : forall (n p: list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
  Crypto_Scalarmult n p = ListofZ32 8 (ZCrypto_Scalarmult (ZofList 8 n) (ZofList 8 p)).
Proof.
  move => n p Hn Hp Hbn Hbp.
  rewrite -Crypto_Scalarmult_Eq => //.
  rewrite ListofZ32_ZofList_Zlength => //.
  all: rewrite -Crypto_Scalarmult_eq.
  all: rewrite /Crypto_Scalarmult_proof.
  2: rewrite /Pack25519.
  2: apply Pack.pack_for_Zlength_32_16.
  2: apply Reduce_by_P.get_t_subst_select_Zlength => //=.
  2: do 3 apply car25519_Zlength.
  apply Pack25519_bound.
  2: apply M_bounded ; assumption.
  all: apply M_Zlength.
  1,3: apply Zlength_a ; assumption.
  all: apply Inv25519_Zlength ; apply Zlength_c ; assumption.
Qed.

Close Scope Z.