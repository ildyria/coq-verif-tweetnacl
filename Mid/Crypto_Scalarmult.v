From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.abstract_fn_rev.
From Tweetnacl Require Import Gen.montgomery_rec.
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

Local Instance Z_Ops : (Ops Z) := Build_Ops Z A Z.mul Z.sub (fun x => Z.mul x x) 121665 Sel25519 Zgetbit.

Definition ZCrypto_Scalarmult n p :=
  let t := Zmontgomery_fn 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).


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
