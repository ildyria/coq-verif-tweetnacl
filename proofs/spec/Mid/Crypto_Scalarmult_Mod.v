From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.AMZubSqSel_Prop.
From Tweetnacl Require Import Gen.abstract_fn_rev.
From Tweetnacl Require Import Gen.montgomery_rec.
From Tweetnacl Require Import Gen.montgomery_rec_eq.
From Tweetnacl Require Import Mid.AMZubSqSel.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Mid.GetBit.
From Tweetnacl Require Import Mid.GetBit_bitn.
From Tweetnacl Require Import Mid.Prep_n.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Mid.Inv25519.
From Tweetnacl Require Import Mid.ScalarMult.
From Tweetnacl Require Import Mid.Mod.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.

From Tweetnacl.Mid Require Import Instances.
Require Import ssreflect.
From stdpp Require Import list.

Open Scope Z.

Lemma abstract_fn_rev_eq_a_Zmod : forall (m p : ℤ) (n pp:Z),
  0 ≤ m →
  modP (P (get_a (abstract_fn_rev m p n 1 pp 0 1 0 0 pp)))
  = modP (get_a (abstract_fn_rev m p n 1%Z (modP pp) 0%Z 1%Z 0%Z 0%Z (modP pp))).
Proof.
  intros m p n pp Hm.
  assert(Heq1:= @abstract_fn_rev_eq_a Z Z Z modP modP Z_Ops Z_Ops Zmod_Z_Eq m p).
  specialize Heq1 with n 1 pp 0 1 0 0 pp.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /Zmod_Z_Eq.
  change (modP 1) with 1%Z.
  change (modP 0) with 0%Z.
  change (id n) with n.
  trivial.
Qed.

Lemma abstract_fn_rev_eq_c_Zmod : forall (m p : ℤ) (n pp:Z),
  0 ≤ m →
  modP (P (get_c (abstract_fn_rev m p n 1 pp 0 1 0 0 pp)))
  = modP (get_c (abstract_fn_rev m p n 1%Z (modP pp) 0%Z 1%Z 0%Z 0%Z (modP pp))).
Proof.
  intros m p n pp Hm.
  assert(Heq1:= @abstract_fn_rev_eq_c Z Z Z modP modP Z_Ops Z_Ops Zmod_Z_Eq m p).
  specialize Heq1 with n 1 pp 0 1 0 0 pp.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /Zmod_Z_Eq.
  change (modP 1) with 1%Z.
  change (modP 0) with 0%Z.
  change (id n) with n.
  trivial.
Qed.

Close Scope Z.