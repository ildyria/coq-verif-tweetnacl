(*sv pack25519(u8 *o,const gf n)
{
  int i,j,b;
  gf m,t;
  FOR(i,16) t[i]=n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  FOR(j,2) {
    m[0]=t[0]- (i64)0xffed;
    for(i=1;i<15;i++) {
      m[i]=t[i]- (i64)0xffff-((m[i-1]>>16)& (i64)1);
      m[i-1]&= (i64)0xffff;
    }
    m[15]=t[15]- (i64)0x7fff-((m[14]>>16)& (i64)1);
    b=(m[15]>>16)& (i64)1;
    m[14]&= (i64)0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]& (unsigned char) 0xff;
    o[2*i+1]=t[i]>>8;
  }
}
*)

Set Warnings "-notation-overridden,-parsing".
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Low Require Import Pack.
From Tweetnacl.Low Require Import Car25519.
From Tweetnacl.Low Require Import Car25519_bounds.
From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Reduce_by_P.
From Tweetnacl.Low Require Import Reduce_by_P_aux.
From Tweetnacl.Low Require Import Reduce_by_P_compose_step.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Sel25519.
From Tweetnacl_verif Require Import init_tweetnacl.
From Tweetnacl_verif Require Import spec_set25519.
From Tweetnacl_verif Require Import spec_sel25519.
From Tweetnacl_verif Require Import spec_car25519.
From Tweetnacl_verif Require Import spec_pack25519.
From Tweetnacl_verif Require Import verif_pack25519_lemmas.

Open Scope Z.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
      ltac:(with_library prog [pack25519_spec; car25519_spec; set25519_spec; sel25519_spec]).

Lemma body_pack25519: semax_body Vprog Gprog f_pack25519 pack25519_spec.
Proof.
start_function.
freeze [2;3;4] F.
do 16 forward.
match goal with
  | [ |- context[field_at _ _ _ ?A _] ] => change A with (mVI64 nil16)
    end.
thaw F.
rename H into Hbn.
rename H0 into Hln.
rename H1 into Hlo.
change (field_at Tsh lg16 [] (mVI64 nil16) v_m) with (data_at Tsh lg16 (mVI64 nil16) v_m).
change (data_at_ Tsh lg16 v_t) with (data_at Tsh lg16 undef16 v_t).
rename n into v_n.
rename o into v_o.
assert(WTSH: writable_share Tsh) by apply writable_share_top.
rename contents_n into n.
freeze [1;2] F.
forward_call (v_t,v_n,Tsh,sh,undef16,n).
thaw F. freeze [0;2;3] F.
forward_call (v_t,Tsh,n).
change (38 * - 2 ^ 47) with (- (38 * 2 ^ 47)) in H.
forward_call (v_t,Tsh,(car25519 n)).
apply verif_pack25519_1 ; assumption.
change (38 * - 2 ^ 47) with (- (38 * 2 ^ 47)) in H0.
forward_call (v_t,Tsh,(car25519 (car25519 n))).
apply verif_pack25519_2 ; assumption.
assert(Hcarcarcar: Forall (fun x : ℤ => 0 <= x < 2 ^ 16) (car25519 (car25519 (car25519 n)))).
apply car25519_bound ; assumption.
clear H H0 H1 (* remove these as we have a stronger Hypothesis live *).

remember (car25519 (car25519 (car25519 n))) as t.
assert(Zlength t = 16).
  by rewrite Heqt ?car25519_Zlength.
thaw F. freeze [1;2] F.
freeze_local L.
rewrite {1}/Sfor.
forward_for_simple_bound 2 (pack25519_Sub F L Tsh v_t v_m t nil16); subst L.
thaw_local.
{
rewrite subst_select_0.
entailer!.
}
{
rename i into j.
remember (get_t (subst_select select_m_t j nil16 t)) as t'.
remember (get_m (subst_select select_m_t j nil16 t)) as m'.
assert(Hlengtht': Zlength t' = 16).
subst t'.
apply get_t_subst_select_Zlength; auto ; omega.
assert(Hboundt': Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t').
subst t'.
apply get_t_subst_select_bound ; try assumption ; try omega ; try reflexivity.
assert(Hlengthm': Zlength m' = 16).
subst m'.
apply get_m_subst_select_Zlength; auto ; omega.
assert(Ht0 : exists t0, Vlong t0 = Znth 0 (mVI64 t') Vundef).
{
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
by rewrite Zlength_map Hlengtht'.
}
destruct Ht0 as [t0 Ht0].
forward ; rewrite -Ht0.
entailer!.
rewrite map_map (Znth_map 0)  in Ht0 ; [|by rewrite Hlengtht'].
inversion Ht0.
assert(Ht'0:= verif_pack25519_4 t' Hlengtht' Hboundt').
(* assert(Int64.min_signed + 65517 <= Znth 0 t' 0  <= Int64.max_signed  + 65517).
omega. *)
forward.
entailer!.
{
remember (car25519 (car25519 (car25519 n))) as t.
remember ((get_t (subst_select select_m_t j nil16 t))) as t'.
rewrite Int64.signed_repr.
assumption.
solve_bounds_by_values_Znth.
}
simpl cast_int_long.

rewrite sub64_repr.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite upd_Znth_map upd_Znth_map.
change (field_at Tsh lg16 [] (mVI64 (upd_Znth 0 m' (Znth 0 t' 0 - 65517))) v_m)
  with (data_at Tsh lg16 (mVI64 (upd_Znth 0 m' (Znth 0 t' 0 - 65517))) v_m).
remember (upd_Znth 0 m' (Znth 0 t' 0 - 65517)) as m''.
assert(Hlengthm'': Zlength m'' = 16).
  by rewrite Heqm'' upd_Znth_Zlength Hlengthm'.
freeze_local L.
forward_for_simple_bound 15 (pack25519_Sub_Step F L Tsh v_t v_m  t' m''); subst L.
thaw_local.
{
rewrite sub_fn_rev_1.
entailer!.
}
{
remember (sub_fn_rev 1 sub_step i m'' t') as m'''.
assert(Hlengthm''': Zlength m''' = 16).
{
subst m'''.
rewrite sub_fn_rev_Zlength ; omega.
}
assert(Ht': exists ti, Vlong ti = (Znth i (mVI64 t') Vundef)).
{
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map.
rewrite Hlengtht'.
omega.
}
destruct Ht' as [ti Hti].
forward ; rewrite -Hti.
entailer!.
assert(Hmi1 : exists mi1, Vlong mi1 = (Znth (i - 1) (mVI64 m''') Vundef)).
{
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map.
rewrite Hlengthm'''.
omega.
}
destruct Hmi1 as [mi1 Hmi1].
forward; rewrite -Hmi1.
entailer!.
rewrite map_map (Znth_map 0) in Hti.
2: omega.
inversion Hti.
rewrite map_map (Znth_map 0) in Hmi1.
2: omega.
inversion Hmi1.
assert(Int64.min_signed + 65536 <= Znth i t' 0  <= Int64.max_signed  + 65535) by
(   apply Forall_Znth ; try omega;
    eapply Forall_impl ; eauto;
    let Hx := fresh in intros ? Hx ;
    simpl in Hx;
    solve_bounds_by_values).
forward.
entailer!.
{
clean_context_from_VST.
remember (car25519 (car25519 (car25519 n))) as t.
remember ((get_t (subst_select select_m_t j nil16 t))) as t'.
remember (get_m (subst_select select_m_t j nil16 t)) as m'.
remember (upd_Znth 0 m' (Znth 0 t' 0 - 65517)) as m''.
apply verif_pack25519_5'; try assumption.
}
forward.
entailer!.
{
clean_context_from_VST.
remember (car25519 (car25519 (car25519 n))) as t.
remember ((get_t (subst_select select_m_t j nil16 t))) as t'.
rewrite upd_Znth_diff ; [ | | | omega].
rewrite (Znth_map Int64.zero).
reflexivity.
all: rewrite ?Zlength_map ?sub_fn_rev_Zlength ?upd_Znth_Zlength ; omega.
}

rewrite Int64.shr_div_two_p.

simpl cast_int_long.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite Int.unsigned_repr.
2: solve_bounds_by_values.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite Int64.unsigned_repr.
2: solve_bounds_by_values.
rewrite and64_repr.
rewrite -H7.
assert(Int64.min_signed + 65536 <= Znth i t' 0  <= Int64.max_signed  + 65535) by
(    apply Forall_Znth ; try omega;
    eapply Forall_impl ; eauto;
    let Hx := fresh in intros ? Hx ;
    simpl in Hx;
    solve_bounds_by_values).
rewrite sub64_repr.
rewrite sub64_repr.
rewrite H7.
do 2 rewrite upd_Znth_map.
rewrite (Znth_map Int64.zero).
2: rewrite Zlength_map upd_Znth_Zlength ; omega.
rewrite (Znth_map 0).
2: rewrite upd_Znth_Zlength ; omega.
forward.
simpl cast_int_long.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite and64_repr.
rewrite upd_Znth_map.
rewrite upd_Znth_map.
entailer!.
replace_cancel.
remember (car25519 (car25519 (car25519 n))) as t.
remember ((get_t (subst_select select_m_t j nil16 t))) as t'.
remember (get_m (subst_select select_m_t j nil16 t)) as m'.
remember (upd_Znth 0 m' (Znth 0 t' 0 - 65517)) as m''.
clean_context_from_VST.
f_equal.
f_equal.
rewrite upd_Znth_diff.
2,3: rewrite ?Zlength_map Hlengthm''' ; omega.
2: omega.
rewrite sub_fn_rev_n.
2: omega.
replace (i + 1 - 1) with i.
2: omega.
remember (sub_fn_rev 1 sub_step i m'' t') as temp.
rewrite /sub_step.
repeat rewrite upd_Znth_upd_nth ; try omega.
rewrite /mod0xffff /subst_0xffffc.
repeat rewrite Znth_nth ; try omega.
f_equal.
f_equal.
f_equal.
f_equal.
rewrite Reduce.Zshiftr_div_pow2_16.
f_equal.
rewrite Int64.signed_repr.
reflexivity.
subst temp.
rewrite /nat_of_Z.
subst m''.
assert(Htemp: - 2 ^ 16 <=
       nth (Z.to_nat (i - 1)) (sub_fn_rev 1 sub_step i (upd_nth 0 m' (subst_0xffed (nth 0 t' 0))) t') 0 < 
       2 ^ 16).
{ apply sub_fn_rev_f_bound_nth ; try assumption; omega. }
rewrite upd_Znth_upd_nth.
rewrite Znth_nth.
rewrite /nat_of_Z.
change (Z.to_nat 0) with 0%nat.
2,3: omega.
rewrite /subst_0xffed in Htemp.
remember (nth (Z.to_nat (i - 1)) (sub_fn_rev 1 sub_step i (upd_nth 0 m' (nth 0 t' 0 - 65517)) t') 0) as temp.
solve_bounds_by_values.
}
remember ((sub_fn_rev 1 sub_step 15 m'' t')) as m'''.
assert(Hlengthm''': Zlength m''' = 16).
{
subst m'''.
rewrite sub_fn_rev_Zlength ; try assumption ; omega.
}
assert(Ht': exists ti, Vlong ti = (Znth 15 (mVI64 t') Vundef)).
{
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map.
rewrite Hlengtht'.
omega.
}
destruct Ht' as [ti Hti].
forward ; rewrite -Hti.
entailer!.
assert(Hmi1 : exists mi1, Vlong mi1 = (Znth 14 (mVI64 m''') Vundef)).
{
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map.
rewrite Hlengthm'''.
omega.
}
destruct Hmi1 as [mi1 Hmi1].
forward; rewrite -Hmi1.
entailer!.
rewrite map_map (Znth_map 0) in Hti.
2: omega.
inversion Hti.
rewrite map_map (Znth_map 0) in Hmi1.
2: omega.
inversion Hmi1.

forward.
entailer!.
remember (car25519 (car25519 (car25519 n))) as t.
remember ((get_t (subst_select select_m_t j nil16 t))) as t'.
rewrite Int64.signed_repr.
remember (Znth 14
              (sub_fn_rev 1 sub_step 15
                 (upd_Znth 0 (get_m (subst_select select_m_t j nil16 t)) (Znth 0 t' 0 - 65517)) t') 0) as mi1.
apply (verif_pack25519_8 t' Hlengtht' Hboundt' H7 mi1) ; try assumption.
try solve[apply Forall_Znth ; [omega|]; eapply list.Forall_impl ; [eassumption |];
intros x Hx ; simpl in Hx ; solve_bounds_by_values].

simpl cast_int_long.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite Int.unsigned_repr.
2: solve_bounds_by_values.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite Int64.shr_div_two_p.
rewrite and64_repr.
rewrite sub64_repr.
rewrite sub64_repr.
rewrite upd_Znth_map.
rewrite upd_Znth_map.
rewrite Int64.unsigned_repr.
2: solve_bounds_by_values.
rewrite Int64.signed_repr.
2: {
subst m'''.
subst m''.
assert(Hntha: forall a, 1 <= a < 16 -> - 2 ^ 16 <= nth (Z.to_nat (a - 1)) (sub_fn_rev 1 sub_step a (upd_nth 0 m' (subst_0xffed (nth 0 t' 0))) t') 0 < 2 ^ 16).
{ intros; apply sub_fn_rev_f_bound_nth ; assumption. }
specialize Hntha with 15.
rewrite ?upd_Znth_upd_nth ?Znth_nth ; try omega.
change (Z.to_nat (15 - 1)) with 14%nat in Hntha.
rewrite /subst_0xffed in Hntha.
change (nat_of_Z 14) with 14%nat.
change (nat_of_Z 0) with 0%nat.
change (Z.to_nat 0) with 0%nat.
assert(Httt: 1 <= 15 < 16) by omega.
apply Hntha in Httt.
remember (nth 14 (sub_fn_rev 1 sub_step 15 (upd_nth 0 m' (nth 0 t' 0 - 65517)) t') 0) as temp.
solve_bounds_by_values.
}
assert(Hmi3 : exists mi2, Vlong mi2 = (Znth 14 (mVI64 (upd_Znth 15 m''' (Znth 15 t' 0 - 32767 - Z.land (Znth 14 m''' 0 / two_p 16) 1))) Vundef)).
{
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map upd_Znth_Zlength Hlengthm''' ; omega.
}
destruct Hmi3 as [mi3 Hmi3].
forward.
entailer!.
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map.
rewrite upd_Znth_Zlength ; omega.
forward.
forward ; rewrite -Hmi3.
entailer!.
rewrite (Znth_map Int64.zero) in Hmi3.
rewrite (Znth_map 0) in Hmi3.
2,3: rewrite ?Zlength_map upd_Znth_Zlength Hlengthm''' ; omega.
forward.
rewrite upd_Znth_diff in Hmi3.
2,3,4: rewrite ?Zlength_map ?Hlengthm''' ; omega.
assert(mi3 = mi1).
congruence.
subst mi3 ; clear Hmi3.
simpl cast_int_long.
rewrite ?Int.signed_repr.
2: solve_bounds_by_values.
subst mi1.
rewrite and64_repr.
rewrite ?upd_Znth_map.
rewrite (Znth_map Int64.zero).
2: rewrite Zlength_map upd_Znth_Zlength ; omega.
rewrite (Znth_map 0).
2: rewrite upd_Znth_Zlength ; omega.

remember (upd_Znth 14 (upd_Znth 15 m''' (Znth 15 t' 0 - 32767 - Z.land (Znth 14 m''' 0 / two_p 16) 1))
           (Z.land (Znth 14 m''' 0) 65535)) as msub.
assert(Hmi2 : exists mi2, Vlong mi2 = Znth 15 (mVI64 msub) Vundef).
{
subst msub.
rewrite (Znth_map Int64.zero).
eexists ; reflexivity.
rewrite Zlength_map.
rewrite upd_Znth_Zlength upd_Znth_Zlength ; omega.
}
destruct Hmi2 as [mi2 Hmi2].
assert(Zlength msub = 16).
{
subst msub.
rewrite ?upd_Znth_Zlength ; omega.
}
rewrite (Znth_map Int64.zero) in Hmi2.
2: rewrite Zlength_map ; omega.
rewrite (Znth_map 0) in Hmi2.
2: omega.
replace (Vlong
                 (Int64.repr
                    (Znth 15 (upd_Znth 15 m''' (Znth 15 t' 0 - 32767 - Z.land (Znth 14 m''' 0 / two_p 16) 1)) 0))) with (Vlong mi2).
2:{
rewrite Hmi2.
subst msub.
f_equal.
f_equal.
rewrite upd_Znth_diff ?upd_Znth_Zlength => // ; omega.
}
rewrite /sem_binary_operation' /sem_and.
simpl.
rewrite Hmi2.
assert (Hmi2_simpl: mi2 = (Int64.repr (Znth 15 msub 0))).
inv Hmi2 => //.
forward.
rewrite Hmi2_simpl.
assert(Htmp:= verif_pack25519_10 (Znth 15 msub 0)).
entailer!.

simpl cast_int_long.
rewrite Hmi2_simpl.
rewrite ?Int.signed_repr.
2: solve_bounds_by_values.
rewrite ?Int.unsigned_repr.
2: solve_bounds_by_values.
rewrite Int64.shr_div_two_p.
rewrite ?Int64.unsigned_repr.
2: solve_bounds_by_values.
rewrite ?Int64.signed_repr.
2: {
subst msub.
rewrite upd_Znth_diff ?upd_Znth_Zlength ; try omega.
rewrite upd_Znth_same ; try omega.
assert(0 <= Z.land (Znth 14 m''' 0 / two_p 16) 1 <= 1).
apply and_0_or_1.
assert(HZland: Z.land (Znth 14 m''' 0 / two_p 16) 1 = 0 \/
  Z.land (Znth 14 m''' 0 / two_p 16) 1 = 1) by omega.
destruct HZland as [HZland | HZland]; rewrite HZland.
1,2: assert(Int64.min_signed + 32767 <= Znth 15 t' 0  <= Int64.max_signed  + 32767).
1,3: apply Forall_Znth ; [omega|]; eapply list.Forall_impl ; [apply Hboundt' |];
intros x Hx ; simpl in Hx ; solve_bounds_by_values.
1,2: repeat rewrite Int64.signed_repr.
split; solve_bounds_by_values.
apply Forall_Znth ; [omega|]; eapply list.Forall_impl ; [apply Hboundt' |];
intros x Hx ; simpl in Hx ; solve_bounds_by_values.
}

rewrite and64_repr.
rewrite sub64_repr.
remember (1 - Z.land (Znth 15 msub 0 / two_p 16) 1) as b'.
deadvars!.
forward_call (v_t, v_m, Tsh, t', msub, b').
repeat split ; auto.
assert(0 <= Z.land (Znth 15 msub 0 / two_p 16) 1 <= 1).
apply and_0_or_1.
omega.
replace (Low.Sel25519 b' t' msub) with (get_t (subst_select select_m_t (j + 1) nil16 t)).
replace (Low.Sel25519 b' msub t') with (get_m (subst_select select_m_t (j + 1) nil16 t)).
entailer!.

all: rewrite subst_select_n.
all: try omega.
all: clean_context_from_VST ; clears.
all: subst msub m''' m'' m' b' t'.
all: replace (j + 1 - 1) with j.
all: try omega.
all: remember (get_m (subst_select select_m_t j nil16 t)) as m'.
all: remember (get_t (subst_select select_m_t j nil16 t)) as t'.
all: rewrite /select_m_t /get_m /get_t.
all: rewrite /GetBit_pack25519.getbit_25519.
all: rewrite Z.shiftr_div_pow2.
all: try omega.
all: rewrite ?upd_Znth_upd_nth ?Znth_nth /nat_of_Z ; try omega.
all: repeat change_Z_to_nat.
all: rewrite /m_from_t /subst_0xffed /mod0xffff /subst_0x7fffc.
all: remember (sub_fn_rev 1 sub_step 15 (upd_nth 0 m' (nth 0 t' 0 - 65517)) t') as tttt0.
all: rewrite ?Int64.Zshiftr_div_two_p.
all: try omega.
all: assert(Zlength tttt0 = 16).
1,3: subst tttt0; rewrite sub_fn_rev_Zlength ?upd_nth_Zlength ; change_Z_of_nat ; omega.
all: change (two_p 16) with (2^16).
1,2: rewrite upd_nth_diff_Zlength.
1,5: rewrite upd_nth_same_Zlength.
1,3: rewrite upd_nth_diff_Zlength.
1,5: rewrite upd_nth_diff_Zlength.
1,5: rewrite upd_nth_same_Zlength.
1,3: reflexivity.
all: rewrite ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
}

thaw F.
freeze [0;3] F.
freeze_local L.
remember (get_t (subst_select select_m_t 2 nil16 t)) as t'.
assert(Ht'length: Zlength t' = 16).
{
subst t'.
apply get_t_subst_select_Zlength.
omega.
reflexivity.
assumption.
}
assert(Ht'bound: Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t').
{
subst t'.
apply get_t_subst_select_bound.
omega.
reflexivity.
assumption.
assumption.
}
rename contents_o into o.
forward_for_simple_bound 16 (pack25519_pack_for F L Tsh tsh v_o v_t o t') ; subst L.
  thaw_local.
  {
  entailer!.
  }
  {
  forward.
  entailer!.
  rewrite map_map (Znth_map 0).
  reflexivity.
  omega.
  rewrite (Znth_map Int64.zero).
  2: rewrite Zlength_map ; omega.
  rewrite (Znth_map 0).
  2: omega.
  forward.
  forward.
  entailer!.
  rewrite map_map (Znth_map 0).
  reflexivity.
  omega.
  forward.
  match goal with
    | |- context[upd_Znth (2 * i + 1) ?A ?B ]=> replace (upd_Znth (2 * i + 1) A B) with (firstn (nat_of_Z (2 * (i + 1))) (mVI (pack_for 8 t')) ++ skipn (nat_of_Z (2 * (i + 1))) o)
    end.
  entailer!.
  replace ((Znth i (mVI64 t') Vundef)) with (Vlong (Int64.repr (Znth i t' 0))).
  2: rewrite map_map (Znth_map 0).
  2: reflexivity.
  2: omega.
  simpl.
  rewrite (Int.signed_repr 255).
  2: solve_bounds_by_values.
  rewrite (and64_repr _ 255).
  rewrite ?Int.zero_ext_and ; try omega.
  rewrite and_repr and_repr.
  rewrite Int64.shr_div_two_p.
  rewrite (Int64.signed_repr (Znth i t' 0)).
  2: {
  clear Heqt' Heqt.
  apply Forall_Znth. 
  omega.
  solve_bounds_by_values_Forall_impl.
  }
  rewrite (Int64.unsigned_repr 8).
  2: solve_bounds_by_values.
  rewrite Int64.unsigned_repr.
  2: {
  split.
  apply Z.land_nonneg ; by right.
  rewrite (Z.land_ones _ 8) ; [|omega].
  assert(2 ^ 8 < Int64.max_unsigned).
  solve_bounds_by_values.
  assert(Znth i t' 0 mod 2 ^ 8 < 2 ^ 8).
  apply Z.mod_pos_bound.
  solve_bounds_by_values.
  omega.
  }
  rewrite (Int64.unsigned_repr (Znth i t' 0 / two_p 8)).
  2: {
  split.
  apply Z_div_pos.
  change (two_p 8) with 256 ; omega.
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  assert(Znth i t' 0 / two_p 8 <= 2^16 / two_p 8).
  apply Z_div_le.
  change (two_p 8) with 256 ; omega.
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  assert(2 ^ 16 / two_p 8 <= Int64.max_unsigned).
  change (two_p 8) with 256 ; solve_bounds_by_values.
  compute ; intros ; discriminate.
  omega.
  }
  remember (mVI (pack_for 8 t')) as r'.
  replace (Vint (Int.repr (Z.land (Z.land (Znth i t' 0) 255) (two_p 8 - 1)))) with (Znth (2*i) r' Vundef).
  rewrite -(upd_Znth_app_step_Zlength (2*i) r' o) ; try omega.
  2: subst r' ; rewrite Zlength_map Zlength_map  pack_for_Zlength_32_16 ; omega.
  replace (2 * (i + 1)) with ((2 * i + 1) + 1) by omega.
  orewrite simple_S_i.
  rewrite (upd_Znth_app_step_Zlength (2 * i + 1) r' o Vundef) ; try omega.
  2: subst r' ; rewrite Zlength_map Zlength_map pack_for_Zlength_32_16 ; omega.
  change (Z.to_nat (2 * i + 1)) with (nat_of_Z (2 * i + 1)).
  rewrite simple_S_i /nat_of_Z ; try omega.
  f_equal.
  {
  subst r'.
  rewrite (Znth_map Int.zero).
  2: rewrite Zlength_map pack_for_Zlength_32_16 ; omega.
  rewrite (Znth_map 0).
  2: rewrite pack_for_Zlength_32_16 ; omega.
  f_equal.
  f_equal.
  rewrite ?Znth_nth ; try omega.
  replace (nat_of_Z (2 * i + 1)) with (2 * nat_of_Z i + 1)%nat.
  2: {
  rewrite nat_of_Z_plus ; try omega.
  rewrite /nat_of_Z.
  rewrite Z2Nat.inj_mul ; try omega.
  reflexivity.
  }
  rewrite pack_for_nth_o.
  change (two_p 8 - 1) with (Z.ones 8).
  rewrite Z.land_ones.
  rewrite Z.mod_small.
  reflexivity.
  2: omega.
  rewrite -Znth_nth ; try omega.
  split.
  apply Z_div_pos.
  change (two_p 8) with 256 ; omega.
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  apply Zdiv_lt_upper_bound.
  change (two_p 8) with 256 ; solve_bounds_by_values.
  change (2 ^ 8 * two_p 8) with (2^16).
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  }
  subst r'.
  rewrite (Znth_map Int.zero).
  2: rewrite Zlength_map pack_for_Zlength_32_16 ; omega.
  rewrite (Znth_map 0).
  2: rewrite pack_for_Zlength_32_16 ; omega.
  f_equal.
  f_equal.
  rewrite ?Znth_nth ; try omega.
  replace (nat_of_Z (2 * i)) with (2 * nat_of_Z i)%nat.
  2: {
  rewrite /nat_of_Z.
  rewrite Z2Nat.inj_mul ; try omega.
  reflexivity.
  }
  rewrite pack_for_nth_e.
  change (two_p 8 - 1) with (Z.ones 8).
  change (255) with (Z.ones 8).
  rewrite Z.land_ones ; try omega.
  rewrite Z.land_ones ; try omega.
  rewrite Z.mod_mod ; solve_bounds_by_values.
  }
  replace (nat_of_Z (2 * 16)) with (Datatypes.length o).
  2: rewrite Zlength_correct in Hlo ; change (nat_of_Z (2 * 16)) with 32%nat ; omega.
  rewrite list.drop_all app_nil_r.
  rewrite Zlength_correct in Hlo.
  rewrite Zlength_correct in Hln.
  replace (Datatypes.length o) with (Datatypes.length (mVI (pack_for 8 t'))).
  2: rewrite ?map_length pack_for_length_32_16.
  2: omega.
  2: rewrite Zlength_correct in Ht'length ; omega.
  rewrite firstn_all.
  thaw F.
  deadvars!.
  subst t'.
  remember (get_m (subst_select select_m_t 2 nil16 t)) as m'.
  remember (get_t (subst_select select_m_t 2 nil16 t)) as t'.
  replace (pack_for 8 t') with (Pack25519 n).
  unfold POSTCONDITION.
  unfold abbreviate.
  eapply semax_return_None with (SEPsf:= [Tsh [{v_m}]<<( lg16 )-- undef16; Tsh [{v_t}]<<( lg16 )-- undef16]); try reflexivity.
  apply return_outer_gen_refl.
  2:  apply return_inner_gen_canon_nil.
  2: {
  change ([sh [{v_n}]<<( lg16 )-- mVI64 n; tsh [{v_o}]<<( uch32 )-- mVI (Pack25519 n)] ++
        [Tsh [{v_m}]<<( lg16 )-- undef16; Tsh [{v_t}]<<( lg16 )-- undef16]) with
        ([sh [{v_n}]<<( lg16 )-- mVI64 n; tsh [{v_o}]<<( uch32 )-- mVI (Pack25519 n) ;
        Tsh [{v_m}]<<( lg16 )-- undef16; Tsh [{v_t}]<<( lg16 )-- undef16]).
  remember (Pack25519 n) as n'.
  entailer!.
  rewrite ?Zlength_map in H3.
  apply Pack25519_bound ; assumption.
  }
  focus_SEP 1.
  unfold stackframe_of.
  eapply canonicalize_stackframe.
  reflexivity.
  unfold f_pack25519.
  simpl fn_vars.
  apply Forall2_cons.
  2: apply Forall2_cons.
  3: apply Forall2_nil.
  apply fn_data_at_intro ; reflexivity.
  apply fn_data_at_intro ; reflexivity.
  subst t'.
  rewrite /Pack25519.
  subst t.
  reflexivity.
Qed.
