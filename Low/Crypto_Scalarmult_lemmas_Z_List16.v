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
From Tweetnacl.Low Require Import AMZubSqSel_Correct.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.
From Tweetnacl.Low Require Import Constant.

Open Scope Z.

Section Crypto_Scalarmult_Eq_ac_List16_Z.

Context (Mod : Z -> Z).
Context (Z_Ops : (Ops Z Z) Mod).
Context (List_Z_Ops : Ops (list Z) (list Z) id).
Context (List_Z_Ops_Prop : @Ops_List List_Z_Ops).
Context (List_Z_Ops_Prop_Correct : @Ops_Prop_List_Z Mod List_Z_Ops Z_Ops).
Local Instance List16_Ops : (Ops (@List16 Z) (List32B) id) := {}.
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
Local Instance List16_Z_Eq : @Ops_Mod_P (@List16 Z) (List32B) Z Mod id List16_Ops Z_Ops := {
P l := (ZofList 16 (List16_to_List l));
P' l := (ZofList 8 (List32_to_List l));
}.
Proof.
- intros [a Ha] [b Hb] ; simpl ; f_equal; apply A_correct.
- intros [a Ha] [b Hb] ; simpl List16_to_List.
  apply mult_GF_Zlengh ; assumption.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; apply Zub_correct.
- intros [a Ha] ; simpl List16_to_List ; apply Sq_GF_Zlengh ; assumption.
- simpl List16_to_List ; f_equal; apply C_121665_correct.
- simpl List16_to_List ; f_equal; apply C_0_correct.
- simpl List16_to_List ; f_equal; apply C_1_correct.
- intros b [p Hp] [q Hq] ; simpl List16_to_List ; f_equal ; apply Sel25519_correct.
- intros b [p Hp] ; simpl ; symmetry ; apply GetBit_correct ; assumption.
Defined.

Lemma abstract_fn_rev_eq_a_Z : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z) (n u:Z),
  0 ≤ m →
  List16_to_List L16ONE = Low.C_1 ->
  List16_to_List L16NUL = Low.C_0 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  ZofList 16 Up = u ->
  ZofList 8 Cn = n ->
  Mod (P (get_a (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP))) =
  Mod (get_a (abstract_fn_rev m p n 1 u 0 1 0 0 u)).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up n u.
  intros Hm.
  intros HL16ONE HL16NUL HL16UP HL32CN.
  intros Hu Hn.
  assert(Heq1:= @abstract_fn_rev_eq_a (List16 Z) List32B Z id Mod List16_Ops Z_Ops List16_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /List16_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN ?Hu ?Hn.
  change (ℤ16.lst Low.C_0) with 0.
  change (ℤ16.lst Low.C_1) with 1.
  trivial.
Qed.

Lemma abstract_fn_rev_eq_c_Z : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z) (n u:Z),
  0 ≤ m →
  List16_to_List L16ONE = Low.C_1 ->
  List16_to_List L16NUL = Low.C_0 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  ZofList 16 Up = u ->
  ZofList 8 Cn = n ->
  Mod (P (get_c (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP))) =
  Mod (get_c (abstract_fn_rev m p n 1 u 0 1 0 0 u)).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up n u.
  intros Hm.
  intros HL16ONE HL16NUL HL16UP HL32CN.
  intros Hu Hn.
  assert(Heq1:= @abstract_fn_rev_eq_c (List16 Z) List32B Z id Mod List16_Ops Z_Ops List16_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /List16_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN ?Hu ?Hn.
  change (ℤ16.lst Low.C_0) with 0.
  change (ℤ16.lst Low.C_1) with 1.
  trivial.
Qed.

End Crypto_Scalarmult_Eq_ac_List16_Z.

Close Scope Z.