From Tweetnacl.Libs Require Import Export.

From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Car25519.

From Tweetnacl.Mid Require Import Prep_n.
From Tweetnacl.Mid Require Import Unpack25519.
From Tweetnacl.Mid Require Import Pack25519.
From Tweetnacl.Mid Require Import Inv25519.
From Tweetnacl.Mid Require Import ScalarMult_rev.
(* From Tweetnacl.Mid Require Import ScalarMult_gen_small. *)
(* From Tweetnacl.Mid Require Import ScalarMult_rev_fn_gen. *)
From Tweetnacl.Mid Require Import AMZubSqSel.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519.

From mathcomp Require Import ssreflect ssrbool eqtype ssralg.

Open Scope Z.

Definition ZCrypto_Scalarmult n p :=
  let t := Zmontgomery_fn 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

Lemma A_ok (a b : Z) : Zmodp.pi (A a b) = (Zmodp.pi a + Zmodp.pi b)%R.
Proof. by rewrite Zmodp_addE. Qed.

Lemma Zub_ok (a b : Z) : Zmodp.pi (Zub a b) = (Zmodp.pi a - Zmodp.pi b)%R.
Proof. by rewrite Zmodp_oppE Zmodp_addE. Qed.

Lemma M_ok (a b : Z) : Zmodp.pi (M a b) = (Zmodp.pi a * Zmodp.pi b)%R.
Proof.
rewrite Zmodp_mulE /M.
apply/eqP; rewrite eqE; apply/eqP=> /=.
unlock p.
by rewrite -!Zcar25519_correct.
Qed.

Lemma Sq_ok (a : Z) : Zmodp.pi (Sq a) = (Zmodp.pi a ^+ 2)%R.
Proof. by rewrite /Sq M_ok GRing.expr2. Qed.

Lemma ZCrypto_Scalarmult_curve25519_ladder n (x : Zmodp.type) :
  ZCrypto_Scalarmult (Z.of_nat n) (val x) = val (curve25519_ladder n x).
Proof. Admitted.

Close Scope Z.
