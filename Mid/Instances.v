From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Mod.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.AMZubSqSel_Prop.
From Tweetnacl Require Import Gen.AMZubSqSel_List.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Mid.AMZubSqSel.
From Tweetnacl Require Import Mid.GetBit.
From Tweetnacl Require Import Mid.GetBit_bitn.

From Tweetnacl.Low Require Import A.
From Tweetnacl.Low Require Import Z.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import S.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl.Low Require Import Sel25519.
From Tweetnacl.Low Require Import GetBit.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg prime div.

Instance Z_Ops : (Ops Z Z modP) := {}.
Proof.
apply Mid.A.
apply Mid.M.
apply Mid.Zub.
apply Mid.Sq.
apply Mid.C_0.
apply Mid.C_1.
apply Mid.C_121665.
apply Mid.Sel25519.
apply Mid.getbit.
move => b * ; rewrite /Mid.Sel25519 ; case (b =? 0) => //.
apply Mid.A_mod_eq.
apply Mid.M_mod_eq.
apply Mid.Zub_mod_eq.
apply Mid.Sq_mod_eq.
move => * ; apply Zmod_mod.
Defined.

Instance Z25519_Ops : (Ops Zmodp.type nat id) := {}.
Proof.
apply Zmodp.add.
apply Zmodp.mul.
apply (fun x y => Zmodp.add x (Zmodp.opp y)).
apply (fun x => Zmodp.mul x x).
apply Zmodp.zero.
apply Zmodp.one.
apply (Zmodp.pi C_121665).
apply (fun b p q => if b =? 0 then p else q).
apply (fun n m => Z.of_nat (ladder.bitn (Z.to_nat (Z.of_nat m)) (Z.to_nat n))).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Defined.

Instance Zmod_Z_Eq : @Ops_Mod_P Z Z Z modP modP Z_Ops Z_Ops := {
P := modP;
P' := id
}.
Proof.
all: move=> * //.
rewrite -Mod_ZA_eq /modP Zmod_mod //.
rewrite -Mod_ZM_eq /modP Zmod_mod //.
rewrite -Mod_ZZub_eq /modP Zmod_mod //.
rewrite -Mod_ZSq_eq /modP Zmod_mod //.
rewrite -Mod_ZSel25519_eq /modP Zmod_mod //.
Defined.

Instance Z25519_Z_Eq : @Ops_Mod_P Zmodp.type nat Z modP id Z25519_Ops Z_Ops := {
P := val;
P' := Z.of_nat
}.
Proof.
intros; simpl; rewrite /A /modP /p -lock Zmod_mod //.
intros; simpl; rewrite /M /modP /p -lock Zmod_mod -Zcar25519_correct -Zcar25519_correct //.
intros; simpl; rewrite /Zub /modP /p -lock Zmod_mod -Zminus_mod_idemp_l Zplus_mod_idemp_r.
change ((2 ^ 255 - 19) :𝓖𝓕) with 0%Z => //=.
intros; simpl; rewrite /Sq /M /modP /p -lock Zmod_mod -Zcar25519_correct -Zcar25519_correct //.
by simpl; rewrite /C_121665 /p -lock.
by simpl; rewrite /C_0 /p -lock.
by simpl; rewrite /C_1 /p -lock.
intros; simpl; rewrite /modP /Mid.Sel25519 ; flatten.
intros; simpl; apply Zgetbit_bitn.
Defined.

Instance List_Z_Ops : Ops (list Z) (list Z) id := {}.
Proof.
apply Low.A.
apply Low.M.
apply Low.Z.
apply Low.S.
apply Low.C_0.
apply Low.C_1.
apply Low.C_121665.
apply Low.Sel25519.
apply Low.getbit.
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.

Instance List_Z_Ops_Prop : (@Ops_List List_Z_Ops) :=  {}.
Proof.
apply A.A_Zlength.
apply M.M_Zlength.
apply Z.Zub_Zlength.
apply S.Sq_Zlength.
apply Sel25519.Sel25519_Zlength.
apply Constant.Zlength_C_121665.
apply Constant.Zlength_C_0.
apply Constant.Zlength_C_1.
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
apply C_0_bounds.
apply C_1_bounds.
Defined.
