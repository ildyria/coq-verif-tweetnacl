From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.

(* From Tweetnacl Require Import Mid.SubList. *)
(* From Tweetnacl Require Import Low.Get_abcdef. *)
(* From Tweetnacl Require Import Low.GetBit_pack25519. *)
(* From Tweetnacl Require Import Low.Sel25519. *)
(* From Tweetnacl Require Import Low.Constant. *)
(* From Tweetnacl Require Import Libs.Lists_extended.
From Tweetnacl Require Import Libs.List_Ltac.
From Tweetnacl Require Import Libs.LibTactics_SF.
From Tweetnacl Require Import Libs.LibTactics.
 *)
 From stdpp Require Import prelude.
Require Import Recdef.
Require Import ssreflect.
Open Scope Z.

Definition subst_c t m := t - (Z.land (Z.shiftr m 16) 1).

Definition sub_step_2 (a:Z) (m:list Z) : list Z :=
    let m' := nth (Z.to_nat (a - 1)) m 0 in
    let t' := nth (Z.to_nat a) m 0 in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (subst_c t' m')) (mod0xffff m').

Lemma sub_step_2_Z_inv : forall a m,
0 < a < Zlength m ->
- 2^16 <= nth (Z.to_nat (a - 1)) m 0 <= 0 ->
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
replace (2 ^ 16 * (- nth (Z.to_nat a) m 0 + (nth (Z.to_nat a) m 0 - Z.land (nth (Z.to_nat (a - 1)) m 0 ≫ 16) 1)) + (- nth (Z.to_nat (a - 1)) m 0 + Z.land (nth (Z.to_nat (a - 1)) m 0) 65535)) with 
(2^16 * (nth (Z.to_nat a) m 0) - 2^16 * (nth (Z.to_nat a) m 0) - 2^16 * (Z.land (nth (Z.to_nat (a - 1)) m 0 ≫ 16) 1) + Z.land (nth (Z.to_nat (a - 1)) m 0) 65535 - nth (Z.to_nat (a - 1)) m 0).
2: ring.
replace (2 ^ 16 * nth (Z.to_nat a) m 0 - 2 ^ 16 * nth (Z.to_nat a) m 0) with 0 by omega.
change 65535 with (Z.ones 16).
change 1 with (Z.ones 1).
rewrite ?Z.land_ones.
change (Z.ones 1) with 1.
2,3: omega.
match goal with
| [ |- ?A = _ ] => replace A with (nth (Z.to_nat (a - 1)) m 0 `mod` 2 ^ 16 - (2 ^ 16 * (nth (Z.to_nat (a - 1)) m 0 ≫ 16) `mod` 2 ^ 1 + nth (Z.to_nat (a - 1)) m 0))
end.
2: omega.
symmetry.
apply Zplus_minus_eq.
rewrite -Zplus_0_r_reverse.
rewrite Zmod_eq.
2: apply pown0 ; omega.
remember (nth (Z.to_nat (a - 1)) m 0) as n.
clear Hm Heqn ; clears.
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

Lemma sub_fn_rev_s_sub_step_2_inv : forall a m,
  0 < a < 16 ->
  Zlength m = 16 ->
  Forall (fun x => - 2^16 <= x <= 0) (take 15 m) ->
  ZofList 16 (sub_fn_rev_s sub_step_2 a m) = ZofList 16 m.
Proof.
intros a m Ha Hm Hb.
(* assert_gen_hyp_ H a 15 14 ; try omega. *)
assert(Hbound: forall a, 0 < a /\ a < 16 -> - 2^16 <= nth (Z.to_nat (a - 1)) m 0 <= 0).
{
  intros x Hx.
  replace(nth (Z.to_nat (x - 1)) m 0) with (nth (Z.to_nat (x - 1)) (take 15 m) 0).
  apply Forall_nth_d.
  compute ; split ; discriminate.
  assumption.
  apply nth_take_full.
  change 15%nat with (Z.to_nat 15).
  apply Z2Nat.inj_lt ; omega.
}
assert(H1: ℤ16.lst sub_fn_rev_s sub_step_2 1 m = ℤ16.lst m).
  rewrite sub_fn_rev_s_1 ; reflexivity.
assert(H2: ℤ16.lst sub_fn_rev_s sub_step_2 2 m = ℤ16.lst m).
  rewrite sub_fn_rev_s_n ; try apply sub_step_2_Z_inv ; try apply Hbound ; try omega.
assert(H3: ℤ16.lst sub_fn_rev_s sub_step_2 3 m = ℤ16.lst m).
  admit.
Admitted.
(* assert(H4: ℤ16.lst sub_fn_rev_s sub_step_2 4 m = ℤ16.lst m).
assert(H5: ℤ16.lst sub_fn_rev_s sub_step_2 5 m = ℤ16.lst m).
assert(H6: ℤ16.lst sub_fn_rev_s sub_step_2 6 m = ℤ16.lst m).
assert(H7: ℤ16.lst sub_fn_rev_s sub_step_2 7 m = ℤ16.lst m).
assert(H8: ℤ16.lst sub_fn_rev_s sub_step_2 8 m = ℤ16.lst m).
assert(H9: ℤ16.lst sub_fn_rev_s sub_step_2 9 m = ℤ16.lst m).
assert(H10: ℤ16.lst sub_fn_rev_s sub_step_2 10 m = ℤ16.lst m).
assert(H11: ℤ16.lst sub_fn_rev_s sub_step_2 11 m = ℤ16.lst m).
assert(H12: ℤ16.lst sub_fn_rev_s sub_step_2 12 m = ℤ16.lst m).
assert(H13: ℤ16.lst sub_fn_rev_s sub_step_2 13 m = ℤ16.lst m).
assert(H14: ℤ16.lst sub_fn_rev_s sub_step_2 14 m = ℤ16.lst m).
assert(H15: ℤ16.lst sub_fn_rev_s sub_step_2 15 m = ℤ16.lst m).
destruct H ; [subst a|].
reflexivity.
destruct H ; [subst a|].

destruct a.
reflexivity.
reflex
induction a.
rewrite 
 *)







Close Scope Z.

