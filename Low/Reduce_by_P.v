From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Get_abcdef.
From Tweetnacl Require Import Low.GetBit_pack25519.
From Tweetnacl Require Import Low.Sel25519.
From Tweetnacl Require Import Low.Constant.
From Tweetnacl Require Import Mid.SubList.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.
From Tweetnacl Require Import Low.Reduce_by_P_compose_1.
From Tweetnacl Require Import Low.Reduce_by_P_compose_2.
From Tweetnacl Require Import Low.Reduce_by_P_compose_1b.
From Tweetnacl Require Import Low.Reduce_by_P_compose_2b.
From Tweetnacl Require Import Low.Reduce_by_P_compose.
From Tweetnacl Require Import Low.Reduce_by_P_aux.
From stdpp Require Import list.
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

(* Definition getBit256 l := Z.land (Z.shiftr (nth 15%nat l 0) 16) 1. *)

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

Lemma ZofList_m_from_t: forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  ZofList 16 (m_from_t m t) = ZofList 16 t - (2^255-19).
Proof.
  intros m t Hm Ht Hbt.
  assert(Hm_nat: (length m = 16)%nat) by (rewrite Zlength_correct in Hm ; omega).
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HForall:= take_15_sub_fn_rev_1 m t Hm Ht Hbt).
  assert(HZl:= HZl m t Hm Ht).
  assert(HZl2:= HZl2 m t Hm Ht).
  rewrite /m_from_t.
  orewrite upd_nth_diff_Zlength.
  orewrite ZofList_upd_nth_Zlength.
  orewrite ZofList_upd_nth_Zlength.
  3: rewrite upd_nth_Zlength.
  all: try (rewrite HZl3 ; change_Z_of_nat ; omega).
  rewrite sub_fn_rev_f_g ; try omega.
  2: rewrite upd_nth_length ; try omega.
  rewrite ?sub_fn_rev_s_sub_step_2_inv.
  2,3,4: try omega ; assumption.

  rewrite sub_fn_rev_s_sub_step_1_inv.
  rewrite upd_nth_same.
  2,3,4: rewrite ?upd_nth_Zlength ?Hm ; change_Z_of_nat ; omega.

  rewrite upd_nth_diff.
  2,3,4: change_Z_of_nat ; omega.

  rewrite upd_nth_diff.
  2,3,4: rewrite Zlength_correct in HZl ; omega.
  rewrite nth_15_m_0 ; try assumption.

  assert(Hbn:= nth_14_bound (sub_fn_rev 1 sub_step_1 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) HZl2 HForall).
  apply ZofList_m_from_t_sub1.
  all: assumption.
Qed.

Lemma firstn_15_m_from_t_bound :
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  Forall (fun x => 0 <= x < 2^16) (firstn (Z.to_nat 15) (m_from_t m t)).
Proof.
  intros m t Hm Ht Hbt.
  assert(Hm_nat: (length m = 16)%nat) by (rewrite Zlength_correct in Hm ; omega).
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HZl1:= HZl m t Hm Ht).
  assert(HZl2:= HZl2 m t Hm Ht).
  assert(HZl3:= HZl3 m t Hm Ht).
  assert(Hmt:= m_from_t_Zlength m t Hm Ht).
  change (Z.to_nat 15) with (Z.to_nat (14 + 1)).
  rewrite -(take_cons_Zlength _ _ 0).
  2: rewrite Hmt ; omega.
  apply Forall_app_2.
  1: {
  unfold m_from_t.
  rewrite upd_nth_take_small_Zlength.
  rewrite upd_nth_take_small_Zlength.
  4: rewrite upd_nth_Zlength.
  all: rewrite ?HZl3.
  all: repeat (change_Z_of_nat ; change_Z_to_nat) ; try omega.
  rewrite sub_fn_rev_f_g ; try omega.
  2: rewrite upd_nth_length ; try omega.
  change 14%nat with (Z.to_nat (15 - 1)).
  apply sub_fn_rev_s_sub_step_2_bound.
  omega. assumption.
  }
  apply Forall_cons_2.
  2: apply Forall_nil_2.
  unfold m_from_t.
  rewrite upd_nth_same_Zlength.
  2: rewrite upd_nth_Zlength ?HZl3.
  all: repeat (change_Z_of_nat ; change_Z_to_nat) ; try omega.
  remember ((nth 14
       (upd_nth 15 (sub_fn_rev 1 sub_step 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t)
          (subst_0x7fffc (nth 15 t 0) (nth 14 (sub_fn_rev 1 sub_step 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) 0))) 0)) as m'.
  rewrite /mod0xffff.
  change 65535 with (Z.ones 16).
  rewrite Z.land_ones.
  apply Z_mod_lt.
  apply pown0.
  all: omega.
Qed.

Lemma nth_15_m_fromt_t_bound :
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
 -32768 <= nth (Z.to_nat 15) (m_from_t m t) 0 < 2^16.
Proof.
  intros m t Hm Ht Hbt.
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HZl3:= HZl3 m t Hm Ht).
  assert(Hmt:= m_from_t_Zlength m t Hm Ht).
  rewrite /m_from_t.
  rewrite upd_nth_diff_Zlength.
  rewrite upd_nth_same_Zlength.
  3,4: rewrite upd_nth_Zlength.
  all: rewrite ?HZl3.
  all: repeat (change_Z_of_nat ; change_Z_to_nat) ; try omega.
  remember (nth 14 (sub_fn_rev 1 sub_step 15 (upd_nth 0 m (subst_0xffed (nth 0 t 0))) t) 0) as n'.
  rewrite /subst_0x7fffc.
  assert(Hz:= and_0_or_1 (n' ≫ 16)).
  assert(0 <= nth 15 t 0 < 2 ^ 16).
  apply Forall_nth_len ; try assumption ; omega.
  omega.
Qed.

Lemma nth_15_m_fromt_t_signed_pos:
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  0 <= nth (Z.to_nat 15) (m_from_t m t) 0 < 2^16
   <-> getbit_25519 (m_from_t m t) = 0.
Proof.
  intros m t Hm Ht Hbt.
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HZl3:= HZl3 m t Hm Ht).
  assert(Hmt:= m_from_t_Zlength m t Hm Ht).
  unfold getbit_25519.
  assert(H216: 2^16 > 0).
  reflexivity.
  assert(H216' : -2^16 < - 32768).
  reflexivity.
  split ; intros.
  assert(Hnhtb:= nth_15_m_fromt_t_bound m t Hm Ht Hbt).
  remember (nth (Z.to_nat 15) (m_from_t m t) 0) as n.
  rewrite Z.shiftr_div_pow2.
  2: omega.

  assert(Hn': n `div` 2 ^ 16 = 0).
  apply Zdiv_small ; omega.
  rewrite Hn'.
  reflexivity.

  assert(Hnhtb:= nth_15_m_fromt_t_bound m t Hm Ht Hbt).
  remember (nth (Z.to_nat 15) (m_from_t m t) 0) as n.
  rewrite Z.shiftr_div_pow2 in H.
  2: omega.
  assert(Hn: n = 0 \/ n < 0 \/ n > 0) by omega.
  destruct Hn as [Hn|[Hn|Hn]].
  omega.
  assert(Hn': n `div` 2 ^ 16 = -1).
    assert(H0: n `div` 2 ^ 16 < 0).
      apply Z.div_lt_upper_bound ; omega.
    assert(H2: (- 2 ^ 16) `div` 2 ^ 16 <= n `div` 2 ^ 16).
      apply Z_div_le; try omega.
    change ((- 2 ^ 16) `div` 2 ^ 16) with (-1) in H2.
    omega.
  rewrite Hn' in H ; simpl in H ; tryfalse.
  omega.
Qed.

Lemma nth_15_m_fromt_t_signed_neg:
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  nth (Z.to_nat 15) (m_from_t m t) 0 < 0
   <-> getbit_25519 (m_from_t m t) = 1.
Proof.
  intros m t Hm Ht Hbt.
  assert(Ht_nat: (length t = 16)%nat) by (rewrite Zlength_correct in Ht ; omega).
  assert(HZl3:= HZl3 m t Hm Ht).
  assert(Hmt:= m_from_t_Zlength m t Hm Ht).
  unfold getbit_25519.
  assert(H216: 2^16 > 0).
  reflexivity.
  assert(H216' : -2^16 < - 32768).
  reflexivity.
  split ; intros.
  assert(Hnhtb:= nth_15_m_fromt_t_bound m t Hm Ht Hbt).
  remember (nth (Z.to_nat 15) (m_from_t m t) 0) as n.
  rewrite Z.shiftr_div_pow2.
  2: omega.
  assert(Hn': n `div` 2 ^ 16 = -1).
    assert(H0: n `div` 2 ^ 16 < 0).
      apply Z.div_lt_upper_bound ; omega.
    assert(H2: (- 2 ^ 16) `div` 2 ^ 16 <= n `div` 2 ^ 16).
      apply Z_div_le; try omega.
    change ((- 2 ^ 16) `div` 2 ^ 16) with (-1) in H2.
    omega.
  rewrite Hn'.
  reflexivity.

  assert(Hnhtb:= nth_15_m_fromt_t_bound m t Hm Ht Hbt).
  remember (nth (Z.to_nat 15) (m_from_t m t) 0) as n.
  rewrite Z.shiftr_div_pow2 in H.
  2: omega.
  assert(Hn: n = 0 \/ n < 0 \/ n > 0) by omega.
  destruct Hn as [Hn|[Hn|Hn]].
  rewrite Hn in H.
  simpl in H ; congruence.
  assumption.

  assert(Hn': n `div` 2 ^ 16 = 0).
  apply Zdiv_small ; omega.
  rewrite Hn' in H.
  simpl in H ; congruence.
Qed.

Lemma getbit_25519_equiv_pos_bound :
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  getbit_25519 (m_from_t m t) = 0 <->
  Forall (fun x => 0 <= x < 2^16) (m_from_t m t).
Proof.
  intros m t Hm Ht Hbt.
  assert(m_from_t_Zlength := m_from_t_Zlength m t Hm Ht).
  assert(Hlen: length (m_from_t m t) = 16%nat).
  rewrite Zlength_correct in m_from_t_Zlength; omega.
  split ; intros.
  {
  apply nth_15_m_fromt_t_signed_pos in H ; try assumption.
  assert(H15:= firstn_15_m_from_t_bound m t Hm Ht Hbt).
  rewrite -(firstn_skipn 16 (m_from_t m t)).
  rewrite drop_ge.
  2: rewrite Hlen ; omega.
  rewrite app_nil_r.
  change 16%nat with (Z.to_nat (15 + 1)).
  rewrite -(take_cons_Zlength _ _ 0).
  2: omega.
  apply Forall_app_2.
  assumption.
  apply Forall_cons_2.
  assumption.
  apply Forall_nil_2.
  }

  assert(H15:= firstn_15_m_from_t_bound m t Hm Ht Hbt).
  assert(Hnhtb:= nth_15_m_fromt_t_bound m t Hm Ht Hbt).
  unfold getbit_25519.
  remember (nth (Z.to_nat 15) (m_from_t m t) 0) as n.
  rewrite Z.shiftr_div_pow2.
  2: omega.
  assert(Hn: n = 0 \/ n < 0 \/ n > 0) by omega.
  destruct Hn as [Hn|[Hn|Hn]].
  rewrite Hn ; reflexivity.
  exfalso.
  assert(ZofList 16 (take (Z.to_nat 15) (m_from_t m t)) < 2^(16*ℤ.ℕ 15)).
  apply ZofList_n_nn_bound_length.
  omega.
  rewrite take_length.
  rewrite Hlen ; reflexivity.
  assumption.
  assert(ℤ16.lst m_from_t m t < 0).
  rewrite -(ZofList_take_nth_drop 16 _ _ 15).
  rewrite drop_ge.
  2: rewrite Hlen ; omega.
  replace (2 ^ (16 * Zlength (take 16 (m_from_t m t))) * (ℤ16.lst [])) with 0.
  replace (Zlength (take 15 (m_from_t m t))) with 15.

  move: H0 ; change_Z_of_nat ; intros.
  assert( 2 ^ (16 * 15) * nth 15 (m_from_t m t) 0 <= -1766847064778384329583297500742918515827483896875618958121606201292619776).
  assert(nth 15 (m_from_t m t) 0 <= -1).
  subst ; move: Hn ; change_Z_to_nat ; intro ; omega.
  replace (2^(16*15)) with 1766847064778384329583297500742918515827483896875618958121606201292619776.
  2: compute ;reflexivity.
  replace (-1766847064778384329583297500742918515827483896875618958121606201292619776) with (1766847064778384329583297500742918515827483896875618958121606201292619776 * (-1)).
  2: compute ;reflexivity.
  omega.
  replace (2^(16*15)) with 1766847064778384329583297500742918515827483896875618958121606201292619776 in H0.
  2: compute ;reflexivity.
  assert(Habc: forall a b c, a < c -> b <= -c -> a + b < 0).
  clear ; intros; omega.
  rewrite Z.add_0_r.
  eapply Habc.
  eassumption.
  eassumption.
  rewrite Zlength_correct take_length Hlen ; reflexivity.
  rewrite Zlength_correct take_length Hlen ; reflexivity.
  omega.
  assert(Hpos: ZList_pos (m_from_t m t)).
  rewrite /ZList_pos.
  eapply Forall_impl.
  eauto.
  clear.
  simpl ; intros ; omega.
  apply (ZofList_pos 16) in Hpos.
  omega.
  omega.
  assert(Hn': n `div` 2 ^ 16 = 0).
  apply Zdiv_small ; omega.
  rewrite Hn'.
  reflexivity.
Qed.

Lemma getbit_25519_equiv_pos :
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  getbit_25519 (m_from_t m t) = 0 <->
  0 <= ZofList 16 (m_from_t m t).
Proof.
  intros m t Hm Ht Hbt.
  assert(m_from_t_Zlength := m_from_t_Zlength m t Hm Ht).
  assert(Hlen: length (m_from_t m t) = 16%nat).
  rewrite Zlength_correct in m_from_t_Zlength; omega.
  split ; intros.
  {
  assert(Forall (fun x => 0 <= x < 2^16) (m_from_t m t)).
  apply getbit_25519_equiv_pos_bound ; assumption.
  apply ZofList_pos.
  omega.
  unfold ZList_pos.
  eapply Forall_impl.
  apply H0.
  clear.
  simpl.
  intros ; omega.
  }

  assert(H15:= firstn_15_m_from_t_bound m t Hm Ht Hbt).
  assert(Hnhtb:= nth_15_m_fromt_t_bound m t Hm Ht Hbt).
  unfold getbit_25519.
  remember (nth (Z.to_nat 15) (m_from_t m t) 0) as n.
  rewrite Z.shiftr_div_pow2.
  2: omega.
  assert(Hn: n = 0 \/ n < 0 \/ n > 0) by omega.
  destruct Hn as [Hn|[Hn|Hn]].
  rewrite Hn ; reflexivity.
  exfalso.
  assert(ZofList 16 (take (Z.to_nat 15) (m_from_t m t)) < 2^(16*ℤ.ℕ 15)).
  apply ZofList_n_nn_bound_length.
  omega.
  rewrite take_length.
  rewrite Hlen ; reflexivity.
  assumption.
  assert(ℤ16.lst m_from_t m t < 0).
  rewrite -(ZofList_take_nth_drop 16 _ _ 15).
  rewrite drop_ge.
  2: rewrite Hlen ; omega.
  replace (2 ^ (16 * Zlength (take 16 (m_from_t m t))) * (ℤ16.lst [])) with 0.
  replace (Zlength (take 15 (m_from_t m t))) with 15.

  move: H0 ; change_Z_of_nat ; intros.
  assert( 2 ^ (16 * 15) * nth 15 (m_from_t m t) 0 <= -1766847064778384329583297500742918515827483896875618958121606201292619776).
  assert(nth 15 (m_from_t m t) 0 <= -1).
  subst ; move: Hn ; change_Z_to_nat ; intro ; omega.
  replace (2^(16*15)) with 1766847064778384329583297500742918515827483896875618958121606201292619776.
  2: compute ;reflexivity.
  replace (-1766847064778384329583297500742918515827483896875618958121606201292619776) with (1766847064778384329583297500742918515827483896875618958121606201292619776 * (-1)).
  2: compute ;reflexivity.
  omega.
  replace (2^(16*15)) with 1766847064778384329583297500742918515827483896875618958121606201292619776 in H0.
  2: compute ;reflexivity.
  assert(Habc: forall a b c, a < c -> b <= -c -> a + b < 0).
  clear ; intros; omega.
  rewrite Z.add_0_r.
  eapply Habc.
  eassumption.
  eassumption.
  rewrite Zlength_correct take_length Hlen ; reflexivity.
  rewrite Zlength_correct take_length Hlen ; reflexivity.
  omega.
  omega.
  assert(Hn': n `div` 2 ^ 16 = 0).
  apply Zdiv_small ; omega.
  rewrite Hn'.
  reflexivity.
Qed.


Lemma getbit_25519_equiv_neg :
  forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  getbit_25519 (m_from_t m t) = 1 <->
  ZofList 16 (m_from_t m t) < 0.
Proof.
  intros m t Hm Ht Hbt.
  assert(m_from_t_Zlength := m_from_t_Zlength m t Hm Ht).
  assert(Hlen: length (m_from_t m t) = 16%nat).
  rewrite Zlength_correct in m_from_t_Zlength; omega.
  split ; intros.
  1: assert(HHH: ℤ16.lst m_from_t m t < 0 \/ 0 <= ℤ16.lst m_from_t m t) by omega.
  2: assert(HHH: getbit_25519 (m_from_t m t) = 1 \/ getbit_25519 (m_from_t m t) = 0) by
    (assert(HHH:= getbit_25519_0_or_1 (m_from_t m t)) ; omega).
  all: destruct HHH as [HHH|HHH] ; try assumption.
  all: apply getbit_25519_equiv_pos in HHH ; try assumption ; omega.
Qed.

Definition select_m_t m t : (list Z * list Z) :=
  let new_m := m_from_t m t in
  let b := 1 - getbit_25519 new_m in
    (Low.Sel25519 b new_m t, Low.Sel25519 b t new_m).

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

Lemma get_t_select_m_t_bound : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  Forall (fun x => 0 <= x < 2^16) (get_t (select_m_t m t)).
Proof.
  intros m t Hm Ht Hbt;
  rewrite /select_m_t /get_m /get_t.
  assert(getbit_25519_dec: getbit_25519 (m_from_t m t) = 0 \/ getbit_25519 (m_from_t m t) = 1).
    assert(GetBit:= getbit_25519_0_or_1 (m_from_t m t)).
    omega.
  destruct getbit_25519_dec as [getbit_25519_dec|getbit_25519_dec];
  rewrite getbit_25519_dec;
  Grind_add_Z ; rewrite /Low.Sel25519 /list_cswap.
  2: rewrite Z.eqb_refl ; assumption.
  destruct (1 =? 0) ; try assumption.
  apply nth_15_m_fromt_t_signed_pos in getbit_25519_dec ; try assumption.
  assert(take15:= firstn_15_m_from_t_bound m t Hm Ht Hbt).
  rewrite -(firstn_skipn 16 (m_from_t m t)).
  assert(m_from_t_Zlength := m_from_t_Zlength m t Hm Ht).
  rewrite drop_ge.
  2: rewrite Zlength_correct in m_from_t_Zlength ; omega.
  rewrite app_nil_r.
  change 16%nat with (Z.to_nat (15 + 1)).
  rewrite -(take_cons_Zlength _ _ 0).
  2: omega.
  apply Forall_app_2.
  assumption.
  apply Forall_cons_2.
  assumption.
  apply Forall_nil_2.
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

Lemma get_t_subst_select_bound : forall i (m t:list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  Forall (fun x => 0 <= x < 2^16) (get_t (subst_select select_m_t i m t)).
Proof.
  intros i m t Hi Hm Ht Hbt.
  assert_gen_hyp i 2 2; [omega|].
  destruct H as [H|[H|H]] ; subst i.
  rewrite subst_select_0 ; simpl ; assumption.
  all: rewrite subst_select_n ; [|omega] ; Grind_add_Z.
  2: rewrite subst_select_n ; [|omega] ; Grind_add_Z.
  all: rewrite subst_select_0.
  all: repeat apply get_t_select_m_t_bound.
  4: apply get_m_select_m_t_Zlength.
  6: apply get_t_select_m_t_Zlength.
  all: simpl ; assumption.
Qed.

Theorem subst_select_red_by_P :
  forall (m t:list Z),
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  red_by_P (ZofList 16 t) = ZofList 16 (get_t (subst_select select_m_t 2 m t)).
Proof.
  intros m t Hm Ht Hbt.
  assert(H25519: - (2 ^ 255 - 19) < 0) by reflexivity.
  assert(HZL1: Zlength (m_from_t m t) = 16).
    repeat apply m_from_t_Zlength ; assumption.
  assert(HZL2: Zlength (m_from_t (m_from_t m t) t) = 16).
    repeat apply m_from_t_Zlength ; assumption.
  assert(HHH: getbit_25519 (m_from_t m t) = 1 \/ getbit_25519 (m_from_t m t) = 0) by
    (assert(HHH:= getbit_25519_0_or_1 (m_from_t m t)) ; omega).
  assert(HHH': getbit_25519 (m_from_t (m_from_t m t) t) = 1 \/ getbit_25519 (m_from_t (m_from_t m t) t) = 0) by
    (assert(HHH':= getbit_25519_0_or_1 (m_from_t (m_from_t m t) t)) ; omega).
  assert(HHH'': getbit_25519 (m_from_t t (m_from_t m t)) = 1 \/ getbit_25519 (m_from_t t (m_from_t m t)) = 0) by
    (assert(HHH'':= getbit_25519_0_or_1 (m_from_t t (m_from_t m t))) ; omega).
  assert(Heqb0 : 0 =? 0 = true). reflexivity.
  assert(Heqb1: 1 =? 0 = false). reflexivity.


  rewrite /red_by_P.
  rewrite subst_select_n ; try omega.
  Grind_add_Z.
  rewrite subst_select_n ; try omega.
  Grind_add_Z.
  rewrite subst_select_0.
  rewrite /get_m /get_t /select_m_t.
  rewrite ZofList_Sel25519.
  rewrite ZofList_Sel25519.
  rewrite ZofList_m_from_t ; try assumption.

  assert(Hsub1: (ℤ16.lst t) < 2^255 - 19 \/ 2^255 - 19 <= (ℤ16.lst t)) by omega.
  destruct Hsub1 as [Hsub1|Hsub1].
  {
  assert(Hsub': (ℤ16.lst t) - (2 ^ 255 - 19) < 0) by omega.
  assert(Hsub'': (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19) < 0) by omega.

  assert(Hbool: (0 <=? (ℤ16.lst t) - (2 ^ 255 - 19)) = false).
    apply Z.leb_gt ; assumption.
  assert(Hbool': (0 <=? (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19)) = false).
    apply Z.leb_gt ; assumption.
  destruct(0 <=? (ℤ16.lst t) - (2 ^ 255 - 19)) eqn:? ; try discriminate.
  destruct(0 <=? (ℤ16.lst t) - (2 ^ 255 - 19)- (2 ^ 255 - 19)) eqn:? ; try discriminate.

  destruct HHH as [HHH|HHH].
  {
  rewrite HHH.
  Grind_add_Z.
  rewrite /Low.Sel25519 /list_cswap.
  destruct (0 =? 0) eqn:? ; try discriminate.
  destruct HHH' as [HHH'|HHH'] ; rewrite HHH'.
  Grind_add_Z.
  destruct (0 =? 0) eqn:? ; try discriminate.
  reflexivity.
  apply getbit_25519_equiv_pos in HHH' ; try assumption;
  rewrite ZofList_m_from_t in HHH' ; try assumption ; omega.
  }
  exfalso.
  apply getbit_25519_equiv_pos in HHH ; try assumption.
  rewrite ZofList_m_from_t in HHH ; try assumption.
  omega.
  }

  assert(Hbool: (0 <=? (ℤ16.lst t) - (2 ^ 255 - 19)) = true).
    apply Zle_imp_le_bool; omega.
    rewrite Hbool.
    assert(getbit_25519 (m_from_t m t) = 0).
    apply getbit_25519_equiv_pos ; try assumption.
    rewrite ZofList_m_from_t ; try assumption; omega.
    rewrite H /Low.Sel25519 /list_cswap.
    Grind_add_Z.
    destruct (1 =? 0) eqn:? ; try discriminate.

  assert(Hsub2: (ℤ16.lst t) - (2^255 - 19) < 2^255 - 19 \/ 2^255 - 19 <= (ℤ16.lst t) - (2^255 - 19)) by omega.
  destruct Hsub2 as [Hsub2|Hsub2].
  {
  assert(Hsub': (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19) < 0) by omega.

  assert(Hbool': (0 <=? (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19)) = false).
    apply Z.leb_gt ; assumption.

  destruct(0 <=? (ℤ16.lst t) - (2 ^ 255 - 19)- (2 ^ 255 - 19)) eqn:? ; try discriminate.
  destruct HHH'' as [HHH''|HHH'']; rewrite HHH'' ; Grind_add_Z.
  destruct (0 =? 0) ; try discriminate ; reflexivity.
  exfalso.
  apply getbit_25519_equiv_pos in HHH'' ; try assumption.
  rewrite ?ZofList_m_from_t in HHH'' ; try assumption.
  omega.
  all: apply getbit_25519_equiv_pos_bound ; assumption.
  }

  assert(Hsub': 0 <= (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19)) by omega.

  assert(Hbool': (0 <=? (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19)) = true).
    apply Zle_imp_le_bool; omega.

  assert(getbit_25519 (m_from_t t (m_from_t m t)) = 0).
  apply getbit_25519_equiv_pos ; try assumption.
  apply getbit_25519_equiv_pos_bound ; assumption.
  rewrite ?ZofList_m_from_t ; try assumption ; try omega.
  apply getbit_25519_equiv_pos_bound ; assumption.
  rewrite H0.
  rewrite ?ZofList_m_from_t ; try assumption ; try omega.
  2: apply getbit_25519_equiv_pos_bound ; assumption.
  Grind_add_Z.
  destruct (1 =? 0) eqn:? ; try discriminate.
  destruct (0 <=? (ℤ16.lst t) - (2 ^ 255 - 19) - (2 ^ 255 - 19)) ; try discriminate ; reflexivity.
Qed.

Corollary subst_select_mod_P :
  forall (m t:list Z),
  Zlength m = 16 ->
  Zlength t = 16 ->
  Forall (fun x => 0 <= x < 2^16) t ->
  ZofList 16 (get_t (subst_select select_m_t 2 m t)) = (ZofList 16 t) mod (2^255-19).
Proof.
  intros. rewrite -subst_select_red_by_P ; try assumption.
  rewrite -reduce_P_is_mod.
  reflexivity.
  split.
  apply ZofList_pos.
  omega.
  unfold ZList_pos.
  eapply Forall_impl; eauto.
  clear ; simpl ; intro ; omega.
  change 256 with (16 * 16%nat).
  apply ZofList_n_nn_bound_Zlength ; go.
Qed.

Close Scope Z.
