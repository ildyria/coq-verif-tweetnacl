From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.abstract_fn_rev.
From Tweetnacl Require Import Gen.montgomery_rec.
From Tweetnacl Require Import Gen.montgomery_rec_eq.
From Tweetnacl Require Import Mid.AMZubSqSel.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Mid.GetBit.
From Tweetnacl Require Import Mid.Prep_n.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Mid.Inv25519.
From Tweetnacl Require Import Mid.ScalarMult.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg.

Open Scope Z.

Section ZCrypto_Scalarmult_gen.

Context (Z_Ops : (Ops Z Z) (fun x => Z.modulo x ((Z.pow 2 255) - 19))).

Definition ZCrypto_Scalarmult_rev_gen n p :=
  let t := abstract_fn_rev 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

Definition ZCrypto_Scalarmult_rec_gen n p :=
  let t := montgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

End ZCrypto_Scalarmult_gen.


Local Instance Z_Ops : (Ops Z Z (fun x => Z.modulo x (Z.pow 2 255 - 19))) := {}.
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
intros b p q ; rewrite /Sel25519 ; flatten.
intros ; apply A_mod_eq.
intros ; apply M_mod_eq.
intros ; apply Zub_mod_eq.
intros ; apply Sq_mod_eq.
intros ; apply Zmod_mod.
Defined.


(* @Timmy this is the definition you want to prove correct with respect to your specifications *)
Definition ZCrypto_Scalarmult n p :=
  let t := Zmontgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

(* This is the equivalence between ladders defined as fn with type class and ladders defined as recursive *)
Theorem ZCrypto_Scalarmult_eq : forall (n p : Z),
  ZCrypto_Scalarmult n p = ZCrypto_Scalarmult_rev_gen Z_Ops n p.
Proof.
  intros.
  rewrite /ZCrypto_Scalarmult /ZCrypto_Scalarmult_rev_gen.
  rewrite /Zmontgomery_rec.
  replace (montgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)) with
  (montgomery_rec (S (Z.to_nat 254)) (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)).
  2: change (S (Z.to_nat 254)) with 255%nat.
  2: reflexivity.
  rewrite montgomery_rec_eq_fn_rev.
  2: omega.
  change (254 + 1) with 255.
  reflexivity.
Qed.

(* Proof of correctness between High and Mid Level *)
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
