From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Mid Require Import Reduce.
From Tweetnacl.Mid Require Import GetBit.
From Tweetnacl.Mid Require Import ScalarMult_gen_small.
From Tweetnacl.Mid Require Import ScalarMult_rev_fn_gen.
From Tweetnacl.Mid Require Import AMZubSqSel.
From Tweetnacl.Mid Require Import ScalarMult_rev.
From Tweetnacl.Mid Require Import ScalarMult_rec_gen.
From Tweetnacl.Mid Require Import ScalarMult_gen.
Require Import ssreflect.


Open Scope Z.
Definition Zabstract_rec := Zabstract_rec Zfa Zfb Zfc Zfd Zfe Zff Zgetbit.
Definition Zmontgomery_rec := Zmontgomery_rec_gen A M Zub Sq c_121665 Sel25519 Zgetbit.

Lemma Zabstract_eq_Zmontgomery_rec : forall n p z a b c d e f,
   Zmontgomery_rec n p z a b c d e f = Zabstract_rec n p z a b c d e f.
Proof.
  induction n ; intros.
  reflexivity.
  rewrite /Zmontgomery_rec /Zabstract_rec.
Admitted.