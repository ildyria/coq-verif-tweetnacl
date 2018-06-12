From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import AMZubSqSel_List.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Low Require Import List16.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl.Low Require Import AMZubSqSel_Correct.
From Tweetnacl.Mid Require Import Crypto_Scalarmult.
From Tweetnacl.Low Require Import ScalarMult_rev.
From Tweetnacl.Low Require Import Crypto_Scalarmult_lemmas_Z_List16.
From Tweetnacl.Low Require Import Crypto_Scalarmult_lemmas_List_List16.
From Tweetnacl.Low Require Import Unpack25519.
From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Inv25519.
From Tweetnacl.Low Require Import Prep_n.
From Tweetnacl.Low Require Import GetBit.
From Tweetnacl.Mid Require Import Unpack25519.
From Tweetnacl.Mid Require Import Pack25519.
From Tweetnacl.Mid Require Import Inv25519.
From Tweetnacl.Mid Require Import Prep_n.

Open Scope Z.

Section Crypto_Scalarmult_Eq_ac_List.

Context (Mod : Z -> Z).
Context (Z_Ops            : (Ops Z Z) Mod).
Context (List_Z_Ops       : Ops (list Z) (list Z) id).
Context (List_Z_Ops_Prop          : @Ops_List List_Z_Ops).
Context (List_Z_Ops_Prop_Correct  : @Ops_Prop_List_Z Mod List_Z_Ops Z_Ops).
Local Instance List16_Ops         : (Ops (@List16 Z) (List32B) id) := {}.
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
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.
Local Instance List16_Z_Eq      : @Ops_Mod_P (@List16 Z) (List32B) Z Mod id List16_Ops Z_Ops := {
P l := (ZofList 16 (List16_to_List l));
P' l := (ZofList 8 (List32_to_List l));
}.
Proof.
- intros [a Ha] [b Hb] ; simpl List16_to_List; rewrite -A_correct; reflexivity.
- intros [a Ha] [b Hb] ; simpl List16_to_List.
  apply mult_GF_Zlengh ; assumption.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; rewrite -Zub_correct; reflexivity.
- intros [a Ha] ; simpl List16_to_List ; apply Sq_GF_Zlengh ; try assumption.
- simpl List16_to_List ; f_equal; rewrite -C_121665_correct ; reflexivity.
- simpl List16_to_List ; f_equal; rewrite -C_0_correct ; reflexivity.
- simpl List16_to_List ; f_equal; rewrite -C_1_correct ; reflexivity.
- intros b [p Hp] [q Hq] ; simpl List16_to_List ; f_equal ; rewrite -Sel25519_correct ; reflexivity.
- intros b [p Hp] ; simpl ; symmetry ; rewrite GetBit_correct ; try assumption ; reflexivity.
Defined.
Local Instance List16_List_Z_Eq : @Ops_Mod_P (List16 Z) (List32B) (list Z) id id List16_Ops List_Z_Ops := {
P := List16_to_List;
P' := List32_to_List
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
Local Lemma abstract_fn_rev_eq_a_Z_List : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z) (n u:Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  ZofList 16 Up = u ->
  ZofList 8 Cn = n ->

  Mod (ZofList 16 (get_a (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up))) =
  Mod (get_a (abstract_fn_rev m p n 1 u 0 1 0 0 u)).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up n u.
  intros Hm.
  intros HL16ONE HL16NUL HL16UP HL32CN.
  intros Hu Hn.
  assert(Heq1:= abstract_fn_rev_eq_a_list List_Z_Ops List_Z_Ops_Prop m p CN L16ONE L16NUL L16UP Cn Up Hm HL16ONE HL16NUL HL16UP HL32CN).
  assert(Heq2:= abstract_fn_rev_eq_a_Z Mod Z_Ops List_Z_Ops List_Z_Ops_Prop 
List_Z_Ops_Prop_Correct m p CN L16ONE L16NUL L16UP Cn Up n u Hm HL16ONE HL16NUL HL16UP HL32CN Hu Hn).
  rewrite -Heq1.
  rewrite -Heq2.
  remember (get_a (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP)) as K.
  destruct K.
  reflexivity.
Qed.


Local Lemma abstract_fn_rev_eq_c_Z_List : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z) (n u:Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  ZofList 16 Up = u ->
  ZofList 8 Cn = n ->

  Mod (ZofList 16 (get_c (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up))) =
  Mod (get_c (abstract_fn_rev m p n 1 u 0 1 0 0 u)).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up n u.
  intros Hm.
  intros HL16ONE HL16NUL HL16UP HL32CN.
  intros Hu Hn.
  assert(Heq1:= abstract_fn_rev_eq_c_list List_Z_Ops List_Z_Ops_Prop m p CN L16ONE L16NUL L16UP Cn Up Hm HL16ONE HL16NUL HL16UP HL32CN).
  assert(Heq2:= abstract_fn_rev_eq_c_Z Mod Z_Ops List_Z_Ops List_Z_Ops_Prop 
List_Z_Ops_Prop_Correct m p CN L16ONE L16NUL L16UP Cn Up n u Hm HL16ONE HL16NUL HL16UP HL32CN Hu Hn).
  rewrite -Heq1.
  rewrite -Heq2.
  remember (get_a (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP)) as K.
  destruct K.
  reflexivity.
Qed.

Lemma abstract_fn_rev_eq_List_Z_a: ∀ (m p : ℤ) Cn Up,
  0 ≤ m →
  Zlength Up = 16 ->
  Forall (fun x => 0 <= x < 2^8) Cn ->
  Mod (ZofList 16 (get_a (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up))) =
  Mod (get_a (abstract_fn_rev m p (ZofList 8 Cn) 1 (ZofList 16 Up) 0 1 0 0 (ZofList 16 Up))).
Proof.
  intros m p Cn Up Hm HUp HCn.
  erewrite <- abstract_fn_rev_eq_a_Z_List.
  reflexivity.
  assumption.
  pose(x := Len One16 Zlength_One16).
  assert( List16_to_List x = One16) by reflexivity.
  eassumption.
  pose(x := Len nul16 Zlength_nul16).
  assert( List16_to_List x = nul16) by reflexivity.
  eassumption.
  pose(x := Len Up HUp).
  assert( List16_to_List x = Up) by reflexivity.
  eassumption.
  pose(x := L32B Cn HCn).
  assert( List32_to_List x = Cn) by reflexivity.
  eassumption.
  reflexivity.
  reflexivity.
Qed.


Lemma abstract_fn_rev_eq_List_Z_c: ∀ (m p : ℤ) Cn Up,
  0 ≤ m →
  Zlength Up = 16 ->
  Forall (fun x => 0 <= x < 2^8) Cn ->
  Mod (ZofList 16 (get_c (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up))) =
  Mod (get_c (abstract_fn_rev m p (ZofList 8 Cn) 1 (ZofList 16 Up) 0 1 0 0 (ZofList 16 Up))).
Proof.
  intros m p Cn Up Hm HUp HCn.
  erewrite <- abstract_fn_rev_eq_c_Z_List.
  reflexivity.
  assumption.
  pose(x := Len One16 Zlength_One16).
  assert( List16_to_List x = One16) by reflexivity.
  eassumption.
  pose(x := Len nul16 Zlength_nul16).
  assert( List16_to_List x = nul16) by reflexivity.
  eassumption.
  pose(x := Len Up HUp).
  assert( List16_to_List x = Up) by reflexivity.
  eassumption.
  pose(x := L32B Cn HCn).
  assert( List32_to_List x = Cn) by reflexivity.
  eassumption.
  reflexivity.
  reflexivity.
Qed.

End Crypto_Scalarmult_Eq_ac_List.


