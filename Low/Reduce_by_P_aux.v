From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.
From Tweetnacl Require Import Low.Reduce_by_P_compose_1.
From Tweetnacl Require Import Low.Reduce_by_P_compose_2.
From Tweetnacl Require Import Low.Reduce_by_P_compose_1b.
From Tweetnacl Require Import Low.Reduce_by_P_compose_2b.
From Tweetnacl Require Import Low.Reduce_by_P_compose.
From Tweetnacl Require Import Mid.SubList.
From Tweetnacl Require Import Low.Get_abcdef.
From Tweetnacl Require Import Low.GetBit_pack25519.
From Tweetnacl Require Import Low.Sel25519.
From Tweetnacl Require Import Low.Constant.
From stdpp Require Import prelude.
Require Import ssreflect.

(*
sv pack25519(u8 *o,const gf n)
{
  int i,j,b;
  gf m,t;
  FOR(i,16) t[i]=n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  FOR(j,2) {
    m[0]=t[0]-0xffed;

    for(i=1;i<15;i++) {
      m[i]=t[i]-0xffff-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }

    m[15]=t[15]-0x7fff-((m[14]>>16)&1);
    b=(m[15]>>16)&1;
    m[14]&=0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]&0xff;
    o[2*i+1]=t[i]>>8;
  }
}
*)

Open Scope Z.

Lemma take_15_sub_fn_rev_1: forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  Forall (λ x : ℤ, - 2 ^ 16 < x ∧ x < 2 ^ 16) (take 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t)).
Proof.
  intros m t Hm Ht Hbt.
  change (15%nat) with (Z.to_nat 15).
  apply sub_fn_rev_s_sub_step_1_bound.
  rewrite upd_nth_Zlength Hm ; go.
  rewrite upd_nth_Zlength Hm ; go.
  assumption.
  destruct t ; [tryfalse|] ; destruct m ; [tryfalse|] ;simpl.
  rewrite firstn_O ; apply Forall_cons_2.
  2: apply Forall_nil ; trivial.
  unfold subst_0xffed.
  apply Forall_cons in Hbt; destruct Hbt.
  change (2^16) with 65536 in * ; omega.
Qed.

Lemma HZl : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (sub_fn_rev_s 1 sub_step_2 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0%Z))) t)) = 16.
Proof.
  intros m t Hm Ht.
  rewrite sub_fn_rev_s_sub_step_2_Zlength.
  all: rewrite ?sub_fn_rev_s_sub_step_1_Zlength.
  all: rewrite ?upd_nth_Zlength; go.
Qed.

Lemma HZl2 : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0%Z))) t) = 16.
Proof.
  intros m t Hm Ht.
  rewrite sub_fn_rev_s_sub_step_1_Zlength.
  all: rewrite ?upd_nth_Zlength; go.
Qed.

Lemma HZl3 : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (sub_fn_rev 1 sub_step 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) = 16.
Proof.
  intros m t Hm Ht.
  rewrite ?sub_fn_rev_Zlength ?upd_nth_Zlength ?Hm ; change_Z_of_nat ; omega.
Qed.

Lemma nth_15_m_0 : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  nth 15 (sub_fn_rev_s 1 sub_step_2 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t)) 0 = nth 15 m 0.
Proof.
  intros m t Hm Ht Hbt.
  assert(Hm_nat: (length m = 16)%nat) by (rewrite Zlength_correct in Hm ; omega).
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HForall:= take_15_sub_fn_rev_1 m t Hm Ht Hbt).
  assert(HZl:= HZl m t Hm Ht).
  assert(HZl2:= HZl2 m t Hm Ht).
  assert(nth 15 m 0 :: nil =
   nth 15 (sub_fn_rev_s 1 sub_step_2 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t)) 0 ::
   drop (S 15) (sub_fn_rev_s 1 sub_step_2 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t))).
  {
  rewrite Zlength_correct in HZl.
  rewrite Zlength_correct in HZl2.
  rewrite -nth_drop.
  change 15%nat with (Z.to_nat 15).
  rewrite sub_fn_rev_f_skip.
  rewrite sub_fn_rev_step_g_last.
  rewrite (nth_drop _ _ 0).
  rewrite upd_nth_diff.
  rewrite drop_ge.
  reflexivity.
  all: try omega.
  all: rewrite upd_nth_length.
  all: omega.
  }
  rewrite drop_ge in H.
  2: rewrite Zlength_correct in HZl ; omega.
  apply ListSame in H ; destruct H.
  symmetry ; assumption.
Qed.

Lemma ZofList_nth_take_cons: forall t,
  (length t = 16)%nat ->
  ℤ16.lst take 15 t = nth 0 t 0 + 65536 * (ℤ16.lst drop 1 (take 15 t)).
Proof.
  intros t Ht.
  destruct t ; [tryfalse|] ; reflexivity.
Qed.

Lemma ZofList_take_nth_last:
  forall t,
  (length t = 16)%nat ->
  ℤ16.lst t = (ℤ16.lst take 15 t) + 65536 * 2 ^ (16 * 14) * nth 15 t 0.
Proof.
  intros t Ht.
  rewrite -(ZofList_take_nth_drop _ _ _ 15).
  2: omega.
  rewrite -Z.add_assoc.
  fequals.
  rewrite drop_ge.
  2: omega.
  change (ℤ16.lst []) with 0.
  rewrite -Zmult_0_r_reverse.
  rewrite Zlength_correct firstn_length_le.
  change_Z_of_nat.
  change (65536 * 2 ^ (16 * 14)) with (2 ^ (16 * 15)).
  omega.
  omega.
Qed.

Lemma n_bounded_null :
  forall n',
  - 2 ^ 16 ≤ n' ∧ n' < 2 ^ 16 ->
  0 = 2 ^ 16 * - Z.land (n' ≫ 16) 1 - n' + n' `mod` 2 ^ 16.
Proof.
  intros n Hbn.
  assert(Hn: n = 0 \/ n < 0 \/ n > 0) by omega.
  rewrite Z.shiftr_div_pow2 ; try omega.

  destruct Hn as [Hn|[Hn|Hn]].
  subst n ; reflexivity.
  assert(Hn': n `div` 2 ^ 16 = -1).
    assert(H0: n `div` 2 ^ 16 < 0).
      apply Z.div_lt_upper_bound ; omega.
    assert(H2: (- 2 ^ 16) `div` 2 ^ 16 <= n `div` 2 ^ 16).
      apply Z_div_le; try omega.
    change ((- 2 ^ 16) `div` 2 ^ 16) with (-1) in H2.
    omega.
  rewrite Hn'.
  change ((-1) `mod` 2 ^ 1 ) with 1.
  change (Z.land (-1) 1) with (1).
  replace (2 ^ 16 * - (1) - n + n `mod` 2 ^ 16) with ((2 ^ 16 * - 1 + n `mod` 2 ^ 16) - n).
  2: ring.
  apply Zplus_minus_eq.
  rewrite -Hn'.
  rewrite -Z_div_mod_eq.
  omega.
  apply pown0 ; omega.
  assert(Hn': n `div` 2 ^ 16 = 0).
  apply Zdiv_small ; omega.
  rewrite Hn'.
  replace (2 ^ 16 * - Z.land 0 1 - n + n `mod` 2 ^ 16) with ((2 ^ 16 * 0 + n `mod` 2 ^ 16) -n).
  2: simpl Z.land ; ring.
  apply Zplus_minus_eq.
  rewrite -Hn'.
  rewrite -Z_div_mod_eq.
  omega.
  apply pown0 ; omega.
Qed.

Lemma nth_14_bound :
  forall t',
  Zlength t' = 16 ->
  Forall (λ x : ℤ, - 2 ^ 16 < x ∧ x < 2 ^ 16) (take 15 t') ->
  -2^16 <= nth 14 (sub_fn_rev_s 1 sub_step_2 15 t') 0 < 2^16.
Proof.
  intros.
  change 15 with (14 + 1).
  change 14%nat with (Z.to_nat 14).
  apply bound_a_subst_step_2_lss ; try omega ; assumption.
Qed.

Lemma ZofList_m_from_t_sub1 : forall 
m t t'',
length m = 16%nat ->
length t = 16%nat ->
- 2 ^ 16 ≤ nth 14 t'' 0 ∧ nth 14 t'' 0 < 2 ^ 16 ->
subst_0xffed (nth 0 t 0) + 2 ^ 16 * (ℤ16.lst take 14 (drop 1 t)) + 2 ^ (16 * 15) * nth 15 m 0 -
1766847064778384329583297500742918515827483896875618958121606201292554240 +
2 ^ (16 * 15%nat) * (- nth 15 m 0 + subst_0x7fffc (nth 15 t 0) (nth 14 t'' 0)) +
2 ^ (16 * 14%nat) * (- nth 14 t'' 0 + mod0xffff (nth 14 t'' 0)) =
(ℤ16.lst t) - (2 ^ 255 - 19).
Proof.
  intros m t t'' Hm_nat Ht_nat Hbt''.
  repeat change_Z_of_nat.
  unfold subst_0xffed.
  replace (2^255 - 19) with 57896044618658097711785492504343953926634992332820282019728792003956564819949.
  2: compute ; reflexivity.
  ring_simplify.

  rewrite take_drop_commute.
  rewrite -ZofList_nth_take_cons.
  2: assumption.
  rewrite /subst_0x7fffc.
  rewrite /mod0xffff.
  change 65535 with (Z.ones 16).
  rewrite Z.land_ones.
  2: omega.
  replace (2 ^ (16 * 15)) with (2 ^ (16 * 14) * 2^16).
  2: reflexivity.
  rewrite -Z.add_assoc.
  rewrite -Z.add_assoc.
  remember (nth 14 t'' 0) as n'.
  replace (2 ^ (16 * 14) * 2 ^ 16 * (nth 15 t 0 - 32767 - Z.land (n' ≫ 16) 1) + (- (2 ^ (16 * 14) * n') + 2 ^ (16 * 14) * n' `mod` 2 ^ 16))
  with (2 ^ (16 * 14) * (2 ^ 16 * (nth 15 t 0 - 32767)) + 2 ^ (16 * 14) * (2 ^ 16 * (- Z.land (n' ≫ 16) 1) - n' +
n' `mod` 2 ^ 16)) by (abstract ring).

  rewrite -n_bounded_null.
  2: assumption.
  ring_simplify.
  change (2147418112* 2^(16*14)) with 57894277771593319327455909206843211008119164848923406400770670397755272200192.
  ring_simplify.
  rewrite -ZofList_take_nth_last.
  reflexivity.
  omega.
Qed.

Lemma sub_fn_rev_f_bound :
  forall (a:nat) m t,
  1 <= a < 16 ->
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (λ x : ℤ, 0 <= x ∧ x < 2 ^ 16) (take (Z.to_nat (a - 1)) (sub_fn_rev 1 sub_step a (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t)).
Proof.
intros a m t Ha Hm Ht.
  assert(Hm_nat: (length m = 16)%nat) by (rewrite Zlength_correct in Hm ; omega).
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HZl:= HZl m t Hm Ht).
  assert(HZl2:= HZl2 m t Hm Ht).
  assert(Zlength (upd_nth 0 m (subst_0xffed (nth 0 t 0))) = 16).
  rewrite upd_nth_Zlength; change_Z_of_nat; omega.
  rewrite sub_fn_rev_f_g ; try omega.
  apply sub_fn_rev_s_sub_step_2_bound.
  2: rewrite sub_fn_rev_s_sub_step_1_Zlength.
  all: try omega.
  rewrite Zlength_correct in H ; omega.
Qed.

Lemma sub_fn_rev_f_bound_nth :
  forall (a:Z) m t,
  1 <= a < 16 ->
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  -2^16 <=  nth (Z.to_nat (a - 1)) (sub_fn_rev 1 sub_step a (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) 0 < 2^16.
Proof.
  intros a m t Ha Hm Ht Hbt.
  assert(Hm_nat: (length m = 16)%nat) by (rewrite Zlength_correct in Hm ; omega).
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HZl:= HZl m t Hm Ht).
  assert(HZl2:= HZl2 m t Hm Ht).
  assert(Zlength (upd_nth 0 m (subst_0xffed (nth 0 t 0))) = 16).
  rewrite upd_nth_Zlength; change_Z_of_nat; omega.
  assert(Haa: a = 1 \/ 1 < a) by omega.
  destruct Haa as [Haa|Haa].
  {
  subst a.
  rewrite sub_fn_rev_1.
  Grind_add_Z.
  change_Z_to_nat.
  rewrite upd_nth_same_Zlength.
  2: change_Z_of_nat ; omega.
  rewrite /subst_0xffed.
  assert(0 <= nth 0 t 0 < 2 ^ 16).
  apply Forall_nth_d.
  split ; reflexivity.
  assumption.
  change (2^16) with 65536 in *.
  omega.
  }
  rewrite sub_fn_rev_f_g ; try omega.
  remember (sub_fn_rev 1 sub_step_1 a (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) as m'.
  replace 
  (sub_fn_rev_s 1 sub_step_2 a m')
  with
  (sub_fn_rev_s 1 sub_step_2 (a - 1 + 1) m').
  apply bound_a_subst_step_2_lss.
  omega.
  subst m'.
  rewrite sub_fn_rev_s_sub_step_1_Zlength ?upd_nth_Zlength ; change_Z_of_nat ;  try omega.
  subst m'.
  2: replace (a - 1 + 1) with a by omega; reflexivity.
  2: rewrite Zlength_correct in H ; omega.
  replace (a - 1 + 1) with a by omega.
  apply sub_fn_rev_s_sub_step_1_bound ; rewrite ?upd_nth_Zlength ; change_Z_of_nat ; try omega.
  assumption.
  destruct m ; [tryfalse|].
  simpl.
  rewrite firstn_O.
  apply Forall_cons_2.
  assert(0 <= nth 0 t 0 < 2^16).
  apply Forall_nth_len ; try assumption; try omega.
  rewrite /subst_0xffed; change (2^16) with 65536 in * ; omega.
  apply Forall_nil_2.
Qed.

Close Scope Z.