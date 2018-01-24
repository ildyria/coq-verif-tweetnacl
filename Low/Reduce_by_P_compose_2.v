From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.
From stdpp Require Import prelude.
Require Import Recdef.
Require Import ssreflect.
Open Scope Z.

Definition subst_c t m := t - (Z.land (Z.shiftr m 16) 1).

Definition sub_step_2 (a:Z) (m:list Z) : list Z :=
    let m' := nth (Z.to_nat (a - 1)) m 0 in
    let t' := nth (Z.to_nat a) m 0 in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (subst_c t' m')) (mod0xffff m').

Lemma sub_step_2_Zlength : forall a m,
  0 < a < Zlength m ->
  Zlength (sub_step_2 a m) = Zlength m.
Proof.
  intros a m Ham.
  rewrite /sub_step_2.
  rewrite ?upd_nth_Zlength.
  reflexivity.
  all: rewrite ?Z2Nat.id.
  all: omega.
Qed.

Lemma sub_fn_rev_s_sub_step_2_ind_Zlength : forall a m,
  0 < a < Zlength m ->
  Zlength (sub_fn_rev_s 1 sub_step_2 a m) = Zlength m ->
  Zlength (sub_fn_rev_s 1 sub_step_2 (a+1) m) = Zlength m.
Proof.
  intros i m Ham Hind.
  rewrite sub_fn_rev_s_equation.
  flatten.
  replace ( i + 1 - 1) with i by omega.
  rewrite <- Hind.
  apply sub_step_2_Zlength.
  rewrite Hind.
  assumption.
Qed.

Lemma sub_fn_rev_s_sub_step_2_Zlength : forall a m,
  0 < a < 16 ->
  Zlength m = 16 ->
  Zlength (sub_fn_rev_s 1 sub_step_2 a m) = Zlength m.
Proof.
  intros.
  pattern a.
  apply P016_impl.
  by rewrite sub_fn_rev_s_1.
  intros ; apply sub_fn_rev_s_sub_step_2_ind_Zlength.
  2: apply H2.
  all: omega.
Qed.

Lemma sub_step_2_Z_inv : forall a m,
0 < a < Zlength m ->
- 2^16 <= nth (Z.to_nat (a - 1)) m 0 <= 0 ->
(* nth (Z.to_nat (a - 1)) m 0 <= 0 -> *)
ZofList 16 (sub_step_2 a m) = ZofList 16 m.
Proof.
intros a m Hm Hbm.
rewrite /sub_step_2 /mod0xffff /subst_c.
rewrite ?ZofList_upd_nth_Zlength.
5: rewrite upd_nth_Zlength.
3,5,6: rewrite Z2Nat.id.
all: try omega.
rewrite Zplus_assoc_reverse.
match goal with
  | [ |- _ + ?A = _ ] => replace A with 0
end.
symmetry.
apply Zplus_0_r_reverse.
replace (16 * Z.to_nat a) with (16 * Z.to_nat (a - 1) + 16).
2: rewrite ?Z2Nat.id ; omega.
rewrite Z.pow_add_r.
2: rewrite ?Z2Nat.id.
2,3,4 : omega.
rewrite Zmult_assoc_reverse.
rewrite Zred_factor4.
symmetry ; rewrite Z.mul_comm; apply Z_eq_mult.
rewrite upd_nth_diff_Zlength.
2,3: rewrite Z2Nat.id.
all: try omega.
2: intro H; apply (f_equal Z.of_nat) in H; rewrite ?Z2Nat.id in H; omega.
change 65535 with (Z.ones 16).
remember (nth _ _ _) as n ; clear Hm Heqn ; clears.
ring_simplify.
repeat match goal with
  | [ |- context[Z.land ?A 1]] => change (Z.land A 1) with (Z.land A (Z.ones 1))
  | _ => rewrite Z.land_ones
  | [ |- ?A - _ + _ - _ = _ ] => replace A with 0 by omega
  | _ => omega
end.
rewrite (Zmod_eq _ (2^16)).
2: apply pown0 ; omega.
rewrite Z.shiftr_div_pow2.
2: omega.
assert(Hn: n = 0 \/ n < 0) by omega.
destruct Hn.
subst n ; reflexivity.

assert(n `div` 2 ^ 16 = -1).
  assert(n `div` 2 ^ 16 < 0).
    apply Z.div_lt_upper_bound ; omega.
  assert((- 2 ^ 16) `div` 2 ^ 16 <= n `div` 2 ^ 16).
    apply Z_div_le; try omega.
  change ((- 2 ^ 16) `div` 2 ^ 16) with (-1) in H1.
  omega.
rewrite H0.
change ((-1) `mod` 2 ^ 1 ) with 1.
ring.
Qed.

Lemma sub_step_2_Z_bound_nth : forall a m,
0 < a < Zlength m ->
- 2^16 < nth (Z.to_nat a) m 0 <= 0 ->
- 2^16 <= nth (Z.to_nat a) (sub_step_2 a m) 0 <= 0.
Proof.
intros a m Hm Hbm.
rewrite /sub_step_2 /mod0xffff /subst_c.
rewrite upd_nth_diff_Zlength ?upd_nth_same_Zlength ?upd_nth_Zlength.
all: try (intro H; apply (f_equal Z.of_nat) in H; rewrite ?Z2Nat.id in H).
all: rewrite ?Z2Nat.id.
assert(Hand: Z.land (nth (Z.to_nat (a - 1)) m 0 ≫ 16) 1 = 0 \/ Z.land (nth (Z.to_nat (a - 1)) m 0 ≫ 16) 1 = 1).
  assert(H:= and_0_or_1 (nth (Z.to_nat (a - 1)) m 0 ≫ 16)) ; omega.
destruct Hand as [Hand|Hand] ; rewrite Hand.
all: try omega.
Qed.

Lemma sub_fn_rev_s_sub_step_2_ind_bound : forall a m,
  0 < a < 16 ->
  Zlength m = 16 ->
  Forall (fun x => 0 <= x < 2^16) (take (Z.to_nat (a - 1)) (sub_fn_rev_s 1 sub_step_2 a m)) ->
  Forall (fun x => 0 <= x < 2^16) (take (Z.to_nat a) (sub_fn_rev_s 1 sub_step_2 (a + 1) m)).
Proof.
  intros i m Ham Hm. intros.
  rewrite sub_fn_rev_s_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega.
  replace ( i + 1 - 1) with i by omega.
  replace (Z.to_nat i) with (Z.to_nat ((i - 1) + 1)).
  2: fequals ; omega.
  rewrite -(take_cons_Zlength _ _ 0).
  2: rewrite sub_step_2_Zlength sub_fn_rev_s_sub_step_2_Zlength; omega.
  remember (sub_fn_rev_s 1 sub_step_2 i m) as m'.
  apply Forall_app_2.
  rewrite /sub_step_2.
  rewrite (upd_nth_alter _ (fun x => (mod0xffff (nth (Z.to_nat (i - 1)) m' 0)))).
  rewrite take_alter.
  2: reflexivity.
  2: omega.
  2: reflexivity.

  Focus 2.
  rewrite upd_nth_length.
  all: replace (length m')%nat with (Z.to_nat (Z.of_nat (length m')))%nat by (apply Nat2Z.id).
  all: rewrite -Z2Nat.inj_lt ; subst.
  all: rewrite -?Zlength_correct.
  4: split.
  all: try omega.
  all: rewrite sub_fn_rev_s_sub_step_2_Zlength ; omega.


  rewrite (upd_nth_alter _ (fun x => (subst_c (nth (Z.to_nat i) m' 0) (nth (Z.to_nat (i - 1)) m' 0)))).
  2: omega.
  2: reflexivity.

  Focus 2.
  replace (length m')%nat with (Z.to_nat (Z.of_nat (length m')))%nat by (apply Nat2Z.id).
  all: rewrite -Z2Nat.inj_lt ; subst.
  all: rewrite -?Zlength_correct.
  all: try omega.
  all: rewrite sub_fn_rev_s_sub_step_2_Zlength ; omega.

  rewrite take_alter.
  assumption.
  rewrite -Z2Nat.inj_le; omega.
  apply Forall_cons_2.
  2: apply Forall_nil ; trivial.

  rewrite /sub_step_2.
  rewrite upd_nth_same_Zlength /mod0xffff.
  change (65535) with (Z.ones 16).
  rewrite Z.land_ones.
  apply Z_mod_lt.
  apply pown0.
  omega.
  omega.
  rewrite upd_nth_Zlength.
  all: subst m'.
  all: rewrite sub_fn_rev_s_sub_step_2_Zlength.
  all: rewrite ?Z2Nat.id; omega.
Qed.

Lemma sub_fn_rev_s_sub_step_2_bound : forall a m,
  0 < a < 16 ->
  Zlength m = 16 ->
  Forall (fun x => 0 <= x < 2^16) (take (Z.to_nat (a - 1)) (sub_fn_rev_s 1 sub_step_2 a m)).
Proof.
  intros.
  pattern a.
  apply P016_impl ; try omega.
  change (Z.to_nat (1 - 1)) with 0%nat.
  rewrite firstn_O ; apply Forall_nil ; trivial.
  intros.
  replace (i + 1 - 1) with i by omega.
  apply sub_fn_rev_s_sub_step_2_ind_bound ; assumption.
Qed.

Close Scope Z.

