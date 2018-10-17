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

From Tweetnacl.High Require Import Zmodp opt_ladder ladder curve25519.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg.

Definition Mod := (fun x => Z.modulo x (Z.pow 2 255 - 19)).

Local Instance Z25519_Ops : (Ops Zmodp.type nat id) := {}.
Proof.
apply Zmodp.add.
apply Zmodp.mul.
apply (fun x y => Zmodp.add x (Zmodp.opp y)).
apply (fun x => Zmodp.mul x x).
apply Zmodp.zero.
apply Zmodp.one.
apply (Zmodp.pi C_121665).
apply (fun b p q => if b =? 0 then p else q).
apply (fun n m => Z.of_nat (bitn (Z.to_nat n) m)).
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

Local Instance Z25519_Z_Eq : @Ops_Mod_P Zmodp.type nat Z Mod id Z25519_Ops Z_Ops := {
P := val;
P' := Z.of_nat
}.
Proof.
intros; simpl. rewrite /A /Mod /p -lock Zmod_mod. reflexivity.
intros; simpl. rewrite /M /Mod /p -lock Zmod_mod -Zcar25519_correct -Zcar25519_correct. reflexivity.
intros; simpl. rewrite /Zub /Mod /p -lock Zmod_mod.
rewrite -Zminus_mod_idemp_l.
change ((2 ^ 255 - 19) :𝓖𝓕) with 0%Z.
rewrite Zplus_mod_idemp_r.
f_equal.
intros; simpl. rewrite /Sq /M /Mod /p -lock Zmod_mod -Zcar25519_correct -Zcar25519_correct. reflexivity.
simpl; rewrite /C_121665 /p -lock. reflexivity.
simpl; rewrite /C_0 /p -lock. reflexivity.
simpl; rewrite /C_1 /p -lock. reflexivity.
intros; simpl.
rewrite /Mod /Sel25519 ; flatten.
intros; simpl.
Admitted.

