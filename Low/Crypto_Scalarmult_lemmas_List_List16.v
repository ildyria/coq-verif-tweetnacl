From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import AMZubSqSel_List.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import abstract_fn_rev.

From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl.Low Require Import List16.


Open Scope Z.

Section Crypto_Scalarmult_Eq_ac_List.

Context (List_Z_Ops : Ops (list Z) (list Z) id).
Context (List_Z_Ops_Prop : @Ops_List List_Z_Ops).
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

Lemma abstract_fn_rev_eq_a_list : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  P (get_a (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP)) =
  get_a (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up.
  intros Hm.
  intros HL16ONE.
  intros HL16NUL.
  intros HL16UP.
  intros HL32CN.
  assert(Heq1:= @abstract_fn_rev_eq_a (List16 Z) List32B (list Z) id id List16_Ops List_Z_Ops List16_List_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /id /P /P' /List16_List_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN.
  trivial.
Qed.

Lemma abstract_fn_rev_eq_c_list : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  P (get_c (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP)) =
  get_c (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up.
  intros Hm.
  intros HL16ONE HL16NUL HL16UP HL32CN.
  assert(Heq1:= @abstract_fn_rev_eq_c (List16 Z) List32B (list Z) id id List16_Ops List_Z_Ops List16_List_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /id /P /P' /List16_List_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN.
  trivial.
Qed.

End Crypto_Scalarmult_Eq_ac_List.

Close Scope Z.