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
From Tweetnacl Require Import Mid.Prep_n.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Mid.Inv25519.
From Tweetnacl Require Import Mid.ScalarMult.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg.

Definition Mod := (fun x => Z.modulo x (Z.pow 2 255 - 19)).

Local Instance Z25519_Ops : (Ops Zmodp.type Zmodp.type id) := {}.
Proof.
apply Zmodp.add.
apply Zmodp.mul.
apply (fun x y => Zmodp.add x (Zmodp.opp y)).
apply (fun x => Zmodp.mul x x).
apply Zmodp.zero.
apply Zmodp.one.
apply (Zmodp.pi C_121665).
apply (fun b p q => if b =? 0 then p else q).
apply (fun n m => Zgetbit n (val m)).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Defined.

Local Instance Z_Ops : (Ops Z Z Mod) := {}.
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

Local Instance Z25519_Z_Eq : @Ops_Mod_P Zmodp.type Zmodp.type Z Mod id Z25519_Ops Z_Ops := {
P := val;
P' := val
}.
Proof.
intros; simpl. admit.
intros; simpl. admit.
intros; simpl. admit.
intros; simpl. admit.
simpl ; rewrite Zmod_small ; [reflexivity| admit].
simpl ; rewrite Zmod_small ; [reflexivity| admit].
simpl ; rewrite Zmod_small ; [reflexivity| admit].
intros; simpl; rewrite /Sel25519; flatten.
intros; simpl ; reflexivity.
Admitted.

