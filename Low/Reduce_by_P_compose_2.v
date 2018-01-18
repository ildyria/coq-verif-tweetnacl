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
  Zlength (sub_fn_rev_s sub_step_2 a m) = Zlength m ->
  Zlength (sub_fn_rev_s sub_step_2 (a+1) m) = Zlength m.
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
  Zlength (sub_fn_rev_s sub_step_2 a m) = Zlength m.
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
  Forall (fun x => 0 <= x < 2^16) m ->
  Forall (fun x => 0 <= x < 2^16) (take (Z.to_nat a - 1) (sub_fn_rev_s sub_step_2 a m)) ->
  Forall (fun x => 0 <= x < 2^16) (take (Z.to_nat a) (sub_fn_rev_s sub_step_2 (a + 1) m)).
Proof.
Admitted.
(*   intros i m Ham Hm.
  rewrite sub_fn_rev_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega.
  replace ( i + 1 - 1) with i by omega.
  rewrite -(take_cons_Zlength _ _ 0).
  2: rewrite sub_step_1_Zlength sub_fn_rev_s_sub_step_1_Zlength; omega.
  remember (sub_fn_rev sub_step_1 i m t) as m'.
  apply Forall_app_2.
  rewrite /sub_step_1.
  rewrite (upd_nth_alter _ (fun x => (subst_0xffff (nth (Z.to_nat i) t 0)))).
  rewrite take_alter.
  2: reflexivity.
  3: reflexivity.
  assumption.
  3: apply Forall_cons_2.
  4: apply Forall_nil ; trivial.
  3: rewrite /sub_step_1;
  rewrite upd_nth_same_Zlength /subst_0xffff.
  3: assert(- 2 ^ 16 + 1 + 65535 ≤ nth (Z.to_nat i) t 0 ∧ nth (Z.to_nat i) t 0 < 1 + 65535) by
    (change(- 2 ^ 16 + 1 + 65535) with 0 ; change(1 + 65535) with (2^16);
    apply Forall_nth_d; [compute ; split; go|assumption]).
  all: try omega.
  apply Nat2Z.inj_lt.
  rewrite -Zlength_correct.
  all: rewrite ?Z2Nat.id ?Heqm' ?sub_fn_rev_s_sub_step_1_Zlength.
  all: try omega.
Qed. *)

(* Lemma sub_fn_rev_s_sub_step_1_bound : forall i m t,
  Zlength m = 16 ->
  0 < i < Zlength m ->
  Forall (fun x => 0 <= x < 2 ^ 16) t ->
  Forall (λ a : ℤ, - 2 ^ 16 + 1 ≤ a ∧ a < 1) (take (Z.to_nat 1) m) ->
  Forall (fun x => -2^16 + 1 <= x < 1) (take (Z.to_nat i) (sub_fn_rev sub_step_1 i m t)).
 *)


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

