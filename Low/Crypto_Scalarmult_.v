From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Gen Require Import AMZubSqSel.
(* From Tweetnacl.Low Require Import AMZubSqSel_Correct. *)
From Tweetnacl.Low Require Import Crypto_Scalarmult.
(* From Tweetnacl.Gen Require Import AMZubSqSel_Prop. *)
From Tweetnacl.Gen Require Import AMZubSqSel_List.
(* From Tweetnacl.Gen Require Import ABCDEF. *)
(* From Tweetnacl.Gen Require Import abstract_fn_rev. *)
(* From Tweetnacl.Gen Require Import abstract_fn_rev_eq. *)
(* From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef. *)
From Tweetnacl.Low Require Import A.
From Tweetnacl.Low Require Import Z.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import S.
(* From Tweetnacl.Low Require Import Pack25519. *)
(* From Tweetnacl.Low Require Import Unpack25519. *)
(* From Tweetnacl.Low Require Import Inv25519. *)
From Tweetnacl.Low Require Import Constant.


Instance List_Z_Ops : Ops (list Z) (list Z) id := {}.
Proof.
apply A.A.
apply M.M.
apply Z.Zub.
apply S.Sq.
apply nul16.
apply One16.
apply Constant.c_121665.
apply Sel25519.Sel25519.
apply GetBit.getbit.
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.

Definition CSM := Crypto_Scalarmult List_Z_Ops.
Instance List_Z_Ops_Prop : (@Ops_List List_Z_Ops) :=  {}.
Proof.
apply A.A_Zlength.
apply M.M_Zlength.
apply Z.Zub_Zlength.
apply S.Sq_Zlength.
apply Sel25519.Sel25519_Zlength.
apply Constant.Zlength_c_121665.
apply Constant.Zlength_c_121665.
apply Constant.Zlength_c_121665.
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
apply nul16_bounds.
apply One16_bounds.
Defined.
(* 
Local Instance List_Z_Ops_Prop_Correct  : @Ops_Prop_List_Z List_Z_Ops Z_Ops := {}.
Proof.
apply A_correct.
intros; simpl.
rewrite mult_GF_Zlengh.
rewrite /M.
rewrite -?Car25519.Zcar25519_correct.
reflexivity.
assumption.
assumption.
apply Zub_correct.
intros. simpl.
rewrite /Sq.
rewrite mult_GF_Zlengh.
rewrite /M.
rewrite -?Car25519.Zcar25519_correct.
reflexivity.
assumption.
assumption.
reflexivity.
reflexivity.
reflexivity.
intros; simpl.
rewrite /Sel25519 /Sel25519.Sel25519 /Sel25519.list_cswap ; flatten.
intros. simpl.
apply getbit_repr.
assumption.
Qed.

Local Instance List16_Ops : (Ops (@List16 Z) (List32B)) := {}.
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
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.

Local Instance List16_List_Z_Eq : @Ops_Mod_P (List16 Z) (List32B) (list Z) List16_Ops List_Z_Ops := {
P := List16_to_List;
P' := List32_to_List;
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

Local Instance List16_Z_Eq : @Ops_Mod_P (@List16 Z) (List32B) Z List16_Ops Z_Ops := {
P l := (ZofList 16 (List16_to_List l));
P' l := (ZofList 8 (List32_to_List l));
}.
Proof.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; apply A_correct.
- intros [a Ha] [b Hb] ; simpl List16_to_List;
rewrite /Mod /M /Z_Ops /AMZubSqSel.M.
rewrite -?Car25519.Zcar25519_correct;
apply mult_GF_Zlengh ; assumption.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; apply Zub_correct.
- intros [a Ha] ; simpl List16_to_List;
rewrite /Mod /S.Sq /Sq /Z_Ops /AMZubSqSel.Sq /AMZubSqSel.M;
rewrite -?Car25519.Zcar25519_correct;
apply mult_GF_Zlengh ; assumption.
- reflexivity.
- reflexivity.
- reflexivity.
- intros b [p Hp] [q Hq] ; simpl List16_to_List ;
rewrite /Sel25519.Sel25519 /Sel25519.list_cswap /Gen.AMZubSqSel.Sel25519 /Z_Ops /Sel25519;
rewrite /Sel25519.list_cswap; flatten.
intros b [p Hp] ; simpl ; symmetry; apply getbit_repr; assumption.
Defined.
 *)
