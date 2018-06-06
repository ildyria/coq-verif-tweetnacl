From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Z.
From Tweetnacl.Low.Reduce_by_P Require Import Reduce_by_P_compose_step.
From Tweetnacl.Low.Reduce_by_P Require Import Reduce_by_P_compose_1.
From Tweetnacl.Low.Reduce_by_P Require Import Reduce_by_P_compose_2.
From Tweetnacl.Low.Reduce_by_P Require Import Reduce_by_P_compose.
From stdpp Require Import list.
Require Import Recdef.
Require Import ssreflect.
Open Scope Z.


Lemma bound_a_subst_step_2 : forall a m,
  0 < a < 15 ->
  Zlength m = 16 ->
  Forall (fun x => -2^16 < x <= 0) (take (Z.to_nat (a + 1)) m) ->
  - 2 ^ 16 ≤ nth (Z.to_nat a) (sub_fn_rev_s 1 sub_step_2 (a + 1) m) 0 ∧ nth (Z.to_nat a) (sub_fn_rev_s 1 sub_step_2 (a + 1) m) 0 ≤ 0.
Proof.
intros.
  rewrite sub_fn_rev_s_n.
  2: omega.
  remember (sub_fn_rev_s 1 sub_step_2 (a + 1 - 1) m) as m'.
  replace (a + 1 - 1) with a by omega.
  rewrite /sub_step_2.
  rewrite upd_nth_diff_Zlength.
  4: intro Ha; apply (f_equal Z.of_nat) in Ha ; repeat rewrite Z2Nat.id in Ha ; omega.
  rewrite upd_nth_same_Zlength.
  2,3,4: subst m' ; rewrite ?upd_nth_Zlength ?Z2Nat.id ?sub_fn_rev_s_sub_step_2_Zlength ; omega.
  rewrite /subst_c.
  assert(Handb:= and_0_or_1 (nth (Z.to_nat (a - 1)) m' 0 ≫ 16)).
  assert(Handbb: Z.land (nth (Z.to_nat (a - 1)) m' 0 ≫ 16) 1 = 0 \/ Z.land (nth (Z.to_nat (a - 1)) m' 0 ≫ 16) 1 = 1) by omega.
  clear Handb.
  assert(- 2 ^ 16 < nth (Z.to_nat a) m' 0 ∧ nth (Z.to_nat a) m' 0 ≤ 0).
  replace (a + 1 - 1) with a in Heqm' by omega.
  {
  rewrite nth_drop_2.
  subst m'.
  rewrite sub_fn_rev_f_skip.
  2: rewrite Zlength_correct in H0.
  2: omega.
  2: omega.
  2: {
  replace (length m')%nat with (Z.to_nat (Z.of_nat (length m')))%nat by (apply Nat2Z.id).
  all: rewrite -Z2Nat.inj_le ; subst.
  all: rewrite -?Zlength_correct.
  all: rewrite ?sub_fn_rev_s_sub_step_2_Zlength ; omega.
  }
  rewrite -nth_drop_2.
  2: {
  replace (length m)%nat with (Z.to_nat (Z.of_nat (length m)))%nat by (apply Nat2Z.id).
  all: rewrite -Z2Nat.inj_le -?Zlength_correct ; omega.
  }
  rewrite -(nth_take_full _ (Z.to_nat (a + 1))).
  2: rewrite -Z2Nat.inj_lt ; omega.
  apply Forall_nth_d.
  compute ; split ; [reflexivity | intros; discriminate].
  change_Z_to_nat.
  assumption.
  }
  destruct Handbb as [Handbb|Handbb] ; rewrite Handbb ;  try omega.
Qed.






Lemma bound_a_subst_step_2_lss : forall a m,
  0 < a < 15 ->
  Zlength m = 16 ->
  Forall (fun x => -2^16 < x < 2^16) (take (Z.to_nat (a + 1)) m) ->
  - 2 ^ 16 ≤ nth (Z.to_nat a) (sub_fn_rev_s 1 sub_step_2 (a + 1) m) 0 ∧ nth (Z.to_nat a) (sub_fn_rev_s 1 sub_step_2 (a + 1) m) 0 < 2^16.
Proof.
intros.
  rewrite sub_fn_rev_s_n.
  2: omega.
  remember (sub_fn_rev_s 1 sub_step_2 (a + 1 - 1) m) as m'.
  replace (a + 1 - 1) with a by omega.
  rewrite /sub_step_2.
  rewrite upd_nth_diff_Zlength.
  4: intro Ha; apply (f_equal Z.of_nat) in Ha ; repeat rewrite Z2Nat.id in Ha ; omega.
  rewrite upd_nth_same_Zlength.
  2,3,4: subst m' ; rewrite ?upd_nth_Zlength ?Z2Nat.id ?sub_fn_rev_s_sub_step_2_Zlength ; omega.
  rewrite /subst_c.
  assert(Handb:= and_0_or_1 (nth (Z.to_nat (a - 1)) m' 0 ≫ 16)).
  assert(Handbb: Z.land (nth (Z.to_nat (a - 1)) m' 0 ≫ 16) 1 = 0 \/ Z.land (nth (Z.to_nat (a - 1)) m' 0 ≫ 16) 1 = 1) by omega.
  clear Handb.
  assert(- 2 ^ 16 < nth (Z.to_nat a) m' 0 ∧ nth (Z.to_nat a) m' 0 < 2^16).
  replace (a + 1 - 1) with a in Heqm' by omega.
  {
  rewrite nth_drop_2.
  subst m'.
  rewrite sub_fn_rev_f_skip.
  2: rewrite Zlength_correct in H0.
  2: omega.
  2: omega.
  2: {
  replace (length m')%nat with (Z.to_nat (Z.of_nat (length m')))%nat by (apply Nat2Z.id).
  all: rewrite -Z2Nat.inj_le ; subst.
  all: rewrite -?Zlength_correct.
  all: rewrite ?sub_fn_rev_s_sub_step_2_Zlength ; omega.
  }
  rewrite -nth_drop_2.
  2: {
  replace (length m)%nat with (Z.to_nat (Z.of_nat (length m)))%nat by (apply Nat2Z.id).
  all: rewrite -Z2Nat.inj_le -?Zlength_correct ; omega.
  }
  rewrite -(nth_take_full _ (Z.to_nat (a + 1))).
  2: rewrite -Z2Nat.inj_lt ; omega.
  apply Forall_nth_d.
  compute ; split ; reflexivity.
  change_Z_to_nat.
  assumption.
  }
  destruct Handbb as [Handbb|Handbb] ; rewrite Handbb ;  try omega.
Qed.

Local Ltac solve_this_assert :=
  rewrite sub_fn_rev_s_n; try omega;
  rewrite sub_step_2_Z_inv_lss; Grind_add_Z; try assumption;
  rewrite ?sub_fn_rev_s_sub_step_2_Zlength ; try omega;
  apply bound_a_subst_step_2_lss ; auto ; try omega;
  eapply Forall_take_n_m ; [| eauto];
  Grind_add_Z ; change_Z_to_nat ; omega.

(*   rewrite sub_fn_rev_s_n; try omega;
  rewrite sub_step_2_Z_inv_lss; Grind_add_Z; try assumption;
  rewrite ?sub_fn_rev_s_sub_step_2_Zlength ; try omega;
  apply bound_a_subst_step_2_lss ; auto ; omega.
 *)
Local Ltac gen_goals P j n := match n with 
  | 0 => idtac
  | n => 
    let n'' := (eval compute in (j - n)) in
    assert(P n'');
    [simpl ; solve_this_assert|];
   let n' := (eval compute in (n - 1)) in
   gen_goals P j n'
  end.

Lemma sub_fn_rev_s_sub_step_2_inv : forall a m,
  0 < a < 16 ->
  Zlength m = 16 ->
  Forall (fun x => - 2^16 < x < 2^16) (take 15 m) ->
  ZofList 16 (sub_fn_rev_s 1 sub_step_2 a m) = ZofList 16 m.
Proof.
intros a m Ha Hm Hb.
assert(Hbound: forall a, 0 < a /\ a < 16 -> - 2^16 < nth (Z.to_nat (a - 1)) m 0 < 2^16).
{
  intros x Hx.
  replace(nth (Z.to_nat (x - 1)) m 0) with (nth (Z.to_nat (x - 1)) (take 15 m) 0).
  apply Forall_nth_d.
  compute ; split ; reflexivity.
  assumption.
  apply nth_take_full.
  change 15%nat with (Z.to_nat 15).
  apply Z2Nat.inj_lt ; omega.
}
assert(H1: ℤ16.lst sub_fn_rev_s 1 sub_step_2 1 m = ℤ16.lst m).
  rewrite sub_fn_rev_s_1 ; reflexivity.
assert(H2: ℤ16.lst sub_fn_rev_s 1 sub_step_2 2 m = ℤ16.lst m).
  rewrite sub_fn_rev_s_n ; try apply sub_step_2_Z_inv_lss; [omega | | omega].
  assert(Haspe: 0 < 2 - 1 /\ 2 - 1 < 16) by omega.
  apply Hbound in Haspe; omega.
(* assert ((fun x => (ℤ16.lst sub_fn_rev_s 1 sub_step_2 x m = ℤ16.lst m)) 3).
  rewrite sub_fn_rev_s_n; try omega;
  rewrite sub_step_2_Z_inv_lss; Grind_add_Z; try assumption;
  rewrite ?sub_fn_rev_s_sub_step_2_Zlength ; try omega;
  apply bound_a_subst_step_2_lss ; auto ; try omega;
  eapply Forall_take_n_m ; [| eauto];
  Grind_add_Z ; change_Z_to_nat ; omega.
 *)
gen_goals (fun x => (ℤ16.lst sub_fn_rev_s 1 sub_step_2 x m = ℤ16.lst m)) 16 13.
assert_gen_hyp_ Hadec a 15 14 ; try omega.
repeat match goal with
  | _ => assumption
  | _ => progress subst
  | [ H : _ \/ _ |- _ ] => destruct H
end.
Qed.

Close Scope Z.