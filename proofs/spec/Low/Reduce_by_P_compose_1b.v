From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Z.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.
From Tweetnacl Require Import Low.Reduce_by_P_compose_1.
From Tweetnacl Require Import Low.Reduce_by_P_compose_2.
From Tweetnacl Require Import Low.Reduce_by_P_compose.
From stdpp Require Import list.
Require Import Recdef.
Require Import ssreflect.
Open Scope Z.

Lemma sub_fn_rev_s_sub_step_1_inv : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  ZofList 16 (sub_fn_rev 1 sub_step_1 15 m t) = nth 0 m 0 +
  2^16 * (ZofList 16 (take 14 (skipn 1 t))) + 2^(16*15) * nth 15 m 0 - 1766847064778384329583297500742918515827483896875618958121606201292554240.
Proof.
intros m t Hm Ht.
assert(Zlength (sub_fn_rev 1 sub_step_1 15 m t) = 16).
rewrite sub_fn_rev_s_sub_step_1_Zlength ; omega.
rewrite -(ZofList_take_drop 16 _ _ 15).
2: omega.
replace (Zlength (take 15 (sub_fn_rev 1 sub_step_1 15 m t))) with 15.
2: rewrite Zlength_correct.
2: rewrite firstn_length.
2: rewrite min_l //.
2: replace (length (sub_fn_rev 1 sub_step_1 15 m t)) with (Z.to_nat (Zlength (sub_fn_rev 1 sub_step_1 15 m t))).
2: rewrite H ; compute ; omega.
2: rewrite Zlength_correct Nat2Z.id //.
rewrite sub_fn_rev_step_g_last.
2: rewrite Zlength_correct in Hm ; omega.
2: rewrite Zlength_correct in Ht ; omega.
rewrite (nth_drop _ _ 0).
2: rewrite Zlength_correct in Hm; omega.
assert(length (sub_fn_rev 1 sub_step_1 15 m t) = 16%nat).
rewrite Zlength_correct in H; omega.
rewrite drop_ge.
2: rewrite Zlength_correct in Hm ; omega.
simpl.
ring_simplify.
rewrite Z.add_comm.
rewrite -Z.add_assoc.
rewrite -Z.add_sub_assoc.
fequals.
rewrite -(firstn_skipn 1 (sub_fn_rev 1 sub_step_1 15 m t)).
remember (sub_fn_rev 1 sub_step_1 15 m t) as m'.
replace (take 15 (take 1 m' ++ drop 1 m')) with (take (length (take 1 m') + 14) (take 1 m' ++ drop 1 m')).
2: fequal ; rewrite take_length_le ; [reflexivity | omega].
rewrite firstn_app_2.
subst.
rewrite sub_fn_rev_step_g_first14.
rewrite sub_fn_rev_g_take.
all: try solve[ rewrite Zlength_correct in Ht; rewrite Zlength_correct in Hm ; omega].
rewrite -(take_cons _ _ 0).
2: rewrite Zlength_correct in Hm; omega.
rewrite firstn_O.
simpl.
rewrite -Z.add_sub_assoc.
fequals.
assert((length t = 16)%nat).
rewrite Zlength_correct in Ht ; omega.
do 17 (destruct t ; [tryfalse |]) ; [| tryfalse].
simpl.
ring.
Qed.

Close Scope Z.
