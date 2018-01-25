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
Require Import Recdef.
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
(*
0xffff = 65535
0xffed = 65517
0x7fff = 32767
*)

Definition subst_0xffed t := t - 65517.
Definition subst_0x7fffc t m := t - 32767 - (Z.land (Z.shiftr m 16) 1).
Definition subst_0x7fff t := t - 32767.

Definition getBit256 l := Z.land (Z.shiftr (nth 15%nat l 0) 16) 1.

Definition m_from_t (m t:list Z) : list Z :=
  let m0 := upd_nth 0 m (subst_0xffed (nth 0 t 0)) in
  let m14 := sub_fn_rev 1 sub_step 15 m0 t in
  let m15 := upd_nth 15 m14 (subst_0x7fffc (nth 15 t 0) (nth 14 m14 0)) in
  upd_nth 14 m15 (mod0xffff (nth 14 m15 0)).

Local Lemma m_from_t_dep_length : forall m m' t,
  (length m = 16)%nat ->
  (length m' = 16)%nat ->
  (length t = 16)%nat ->
  m_from_t m' t = m_from_t m t.
Proof.
  intros.
  do 17 (destruct m ; [tryfalse |]) ; [|tryfalse].
  do 17 (destruct m' ; [tryfalse |]) ; [|tryfalse].
  do 17 (destruct t ; [tryfalse |]) ; [|tryfalse].
  unfold m_from_t.
  simpl nth; simpl upd_nth.
  reflexivity.
Qed.

Lemma m_from_t_dep_Zlength : forall m m' t,
  Zlength m = 16 ->
  Zlength m' = 16 ->
  Zlength t = 16 ->
  m_from_t m' t = m_from_t m t.
Proof. convert_length_to_Zlength m_from_t_dep_length. Qed.

Definition select_m_t m t : (list Z * list Z) :=
  let new_m := m_from_t m t in 
  let b := 1 - getbit_25519 new_m in
    (Sel25519 b new_m t, Sel25519 b t new_m).

Lemma m_from_t_Zlength : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (m_from_t m t) = 16.
Proof.
  intros m t Hm Ht.
  rewrite /m_from_t.
  repeat first[
    omega
    | rewrite sub_fn_rev_Zlength 
    | rewrite upd_nth_Zlength
    | change_Z_of_nat ; omega].
Qed.

(*
Lemma sub_fn_rev_s_sub_step_2_inv : forall a m,
  0 < a < 16 ->
  Zlength m = 16 ->
  Forall (fun x => - 2^16 < x <= 0) (take 15 m) ->
  ZofList 16 (sub_fn_rev_s 1 sub_step_2 a m) = ZofList 16 m.
*)

(*
Lemma sub_fn_rev_s_sub_step_1_bound : forall i m t,
  Zlength m = 16 ->
  0 < i < Zlength m ->
  Forall (fun x => 0 <= x < 2 ^ 16) t ->
  Forall (λ a : ℤ, - 2 ^ 16 < a ∧ a < 2^16) (take (Z.to_nat 1) m) ->
  Forall (fun x => -2^16 < x < 2^16) (take (Z.to_nat i) (sub_fn_rev 1 sub_step_1 i m t)).
*)

(*
Lemma sub_fn_rev_s_sub_step_1_inv : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  ZofList 16 (sub_fn_rev 1 sub_step_1 15 m t) = nth 0 m 0 +
  2^16 * (ZofList 16 (take 14 (skipn 1 t))) + 2^(16*15) * nth 15 m 0 - 1766847064778384329583297500742918515827483896875618958121606201292554240.
 *)


Definition m_from_t_loops (m t:list Z) : list Z :=
  let m0 := upd_nth 0 m (subst_0xffed (nth 0 t 0)) in
  sub_fn_rev 1 sub_step 15 m0 t.

Lemma ZofList_m_from_t: forall m t, 
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  ZofList 16 (m_from_t m t) = ZofList 16 t - (2^255-19).
Proof.
  intros m t Hm Ht Hbt.
  assert(Hm_nat: (length m = 16)%nat) by (rewrite Zlength_correct in Hm ; omega).
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HForall: Forall (λ x : ℤ, - 2 ^ 16 < x ∧ x < 2 ^ 16) (take 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t))).
  {
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
  }
  assert(HZl: Zlength (sub_fn_rev_s 1 sub_step_2 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0%Z))) t)) = 16).
  {
  rewrite sub_fn_rev_s_sub_step_2_Zlength.
  all: rewrite ?sub_fn_rev_s_sub_step_1_Zlength.
  all: rewrite ?upd_nth_Zlength; go.
  }
  assert(HZl2: Zlength (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0%Z))) t) = 16).
  {
  rewrite sub_fn_rev_s_sub_step_1_Zlength.
  all: rewrite ?upd_nth_Zlength; go.
  }
  rewrite /m_from_t.
  rewrite upd_nth_diff_Zlength.
  2,3,4: rewrite ?sub_fn_rev_Zlength ?upd_nth_Zlength ?Hm ; go.
  rewrite ZofList_upd_nth_Zlength.
  rewrite ZofList_upd_nth_Zlength.
  2,4: omega.
  3: rewrite upd_nth_Zlength.
  2,3,4 : rewrite sub_fn_rev_Zlength.
  2,3,4,5,6,7,8,9,10: rewrite upd_nth_Zlength Hm ;go.
  rewrite sub_fn_rev_f_g ; try omega.
  2: rewrite upd_nth_length ; try omega.
  rewrite ?sub_fn_rev_s_sub_step_2_inv.
  2,3,4: go.

  rewrite sub_fn_rev_s_sub_step_1_inv.
  rewrite upd_nth_same.
  2,3,4: rewrite ?upd_nth_Zlength ?Hm ; go.

  rewrite upd_nth_diff.
  2,3,4: go.

  rewrite upd_nth_diff.
  2,3: rewrite Zlength_correct in HZl.
  2,3,4: omega.
  replace (nth 15 (sub_fn_rev_s 1 sub_step_2 15 (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t)) 0) with 
  (nth 15 m 0).

  Focus 2.
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
  assumption.
  remember (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) as t'.
  repeat change_Z_of_nat.
  unfold subst_0xffed.
  ring_simplify.

  rewrite take_drop_commute.
  simpl.
  replace (nth 0 t 0 + 65536 * (ℤ16.lst drop 1 (take 15 t))) with (ℤ16.lst (take 15 t)).
  2: destruct t ; [tryfalse|] ; reflexivity.
  remember (nth 14 (sub_fn_rev_s 1 sub_step_2 15 t') 0) as n'.
  assert(-2 ^16 <= n' < 2^16).
  {
  subst n'.
  change 15 with (14 + 1).
  change 14%nat with (Z.to_nat 14).
  apply bound_a_subst_step_2_lss ; try omega ; assumption.
  }
  rewrite /subst_0x7fffc.
  rewrite /mod0xffff.
  change 65535 with (Z.ones 16).
  rewrite Z.land_ones.
  2: omega.
  replace (2 ^ (16 * 15)) with (2 ^ (16 * 14) * 2^16).
  2: reflexivity.
  rewrite -Z.add_assoc.
  rewrite -Z.add_assoc.
  replace (2 ^ (16 * 14) * 2 ^ 16 * (nth 15 t 0 - 32767 - Z.land (n' ≫ 16) 1) + (- (2 ^ (16 * 14) * n') + 2 ^ (16 * 14) * n' `mod` 2 ^ 16))
  with (2 ^ (16 * 14) * (2 ^ 16 * (nth 15 t 0 - 32767)) + 2 ^ (16 * 14) * (2 ^ 16 * (- Z.land (n' ≫ 16) 1) - n' +
n' `mod` 2 ^ 16)).
  2: ring.
  replace (2 ^ 16 * - Z.land (n' ≫ 16) 1 - n' + n' `mod` 2 ^ 16) with 0.
  ring_simplify.
  change (2147418112* 2^(16*14)) with 57894277771593319327455909206843211008119164848923406400770670397755272200192.
  ring_simplify.
  replace ((ℤ16.lst take 15 t) + 65536 * 2 ^ (16 * 14) * nth 15 t 0) with (ℤ16.lst t).
  reflexivity.
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
  rewrite Z.shiftr_div_pow2 ; try omega.
  clear Heqn' HZl2 HZl Heqt' Hm_nat Ht_nat Hm Ht Hbt.
  clears.
  rename n' into n.
  assert(Hn: n = 0 \/ n < 0 \/ n > 0) by omega.
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

Lemma get_m_select_m_t_Zlength : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (get_m (select_m_t m t)) = 16.
Proof.
  intros m t Hm Ht;
  rewrite /select_m_t /get_m /get_t;
  apply Sel25519_Zlength ; try apply m_from_t_Zlength; assumption.
Qed.

Lemma get_t_select_m_t_Zlength : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (get_t (select_m_t m t)) = 16.
Proof.
  intros m t Hm Ht;
  rewrite /select_m_t /get_m /get_t;
  apply Sel25519_Zlength ; try apply m_from_t_Zlength; assumption.
Qed.


Function subst_select (f: list Z -> list Z -> list Z*list Z) (a:Z) (m t: list Z) {measure Z.to_nat a} : (list Z*list Z) :=
  if (a <=? 0)
    then (m,t)
    else
      let m_prev := get_m (subst_select f (a - 1) m t) in 
      let t_prev := get_t (subst_select f (a - 1) m t) in 
        (f m_prev t_prev).
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma subst_select_0 : forall f m t,
  subst_select f 0 m t = (m,t).
Proof. go. Qed.

Lemma subst_select_n : forall a m t f,
  0 < a ->
  subst_select f a m t = (f (get_m (subst_select f (a - 1) m t)) (get_t (subst_select f (a - 1) m t))).
Proof. intros. rewrite subst_select_equation.
flatten ; apply Zle_bool_imp_le in Eq; omega.
Qed.

Lemma get_m_subst_select_f_Zlength : forall i (m t:list Z) (f: list Z -> list Z -> list Z * list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_m (f m' t')) = 16) ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_t (f m' t')) = 16) ->
    Zlength (get_m (subst_select f i m t)) = 16.
Proof.
  intros i m t f Hi Hm Ht Hfm Hft.
  assert_gen_hyp i 2 2; [omega|].
  destruct H as [H|[H|H]] ; subst i;
  try solve [rewrite subst_select_n ; go] ; go.
Qed.

Lemma get_t_subst_select_f_Zlength : forall i (m t:list Z) (f: list Z -> list Z -> list Z * list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_m (f m' t')) = 16) ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_t (f m' t')) = 16) ->
    Zlength (get_t (subst_select f i m t)) = 16.
Proof.
  intros i m t f Hi Hm Ht Hfm Hft.
  assert_gen_hyp i 2 2; [omega|].
  destruct H as [H|[H|H]] ; subst i;
  try solve [rewrite subst_select_n ; go] ; go.
Qed.

Lemma get_m_subst_select_Zlength : forall i (m t:list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
    Zlength (get_m (subst_select select_m_t i m t)) = 16.
Proof.
  intros. apply get_m_subst_select_f_Zlength ; auto.
  apply get_m_select_m_t_Zlength.
  apply get_t_select_m_t_Zlength.
Qed.

Lemma get_t_subst_select_Zlength : forall i (m t:list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
    Zlength (get_t (subst_select select_m_t i m t)) = 16.
Proof.
  intros. apply get_t_subst_select_f_Zlength ; auto.
  apply get_m_select_m_t_Zlength.
  apply get_t_select_m_t_Zlength.
Qed.

Close Scope Z.