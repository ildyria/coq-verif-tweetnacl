(* r=(z[i>>3]>>(i&7))&1; *)

Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Mid.GetBit.
Require Import ssreflect.
Require Import stdpp.list.

Open Scope Z.

Module Low.
Definition getbit (i:Z) (l : list Z) := Z.land ((Z.shiftr (nth (Z.to_nat (Z.shiftr i 3)) l 0)  (Z.land (Z.of_nat (Z.to_nat i)) 7))) 1.
End Low.

Lemma getbit_0_or_1 i l: 0 <= Low.getbit i l <= 1.
Proof. apply and_0_or_1. Qed.

Local Lemma Forall_Pos_bound : forall l, Forall (fun x => 0 <= x < 2^8) l -> ZofList 8 l <? 0 = false.
Proof.
intros l Hl.
have : 0 <= ZofList 8 l.
{
apply ZofList_pos => //.
eapply list.Forall_impl.
apply Hl.
intro => /= ; omega.
}
apply Z.ltb_ge ; assumption.
Qed.

Local Lemma getbit_minus : forall l i,
  i < 0->
  Forall (fun x => 0 <= x < 2^8) l ->
  Mid.getbit i (ZofList 8 l) = Low.getbit i l.
Proof.
rewrite /Low.getbit /Mid.getbit.
move=> l i Hi Hl.
rewrite Forall_Pos_bound; [|assumption].
have ->: (i <? 0) = true.
  apply Z.ltb_lt ; assumption.
have ->: (Z.to_nat (i ≫ 3) = Z.to_nat 0).
  have Hin: i ≫ 3 < 0.
  by apply Z.shiftr_neg.
  rewrite Z_to_nat_nonpos //.
  omega.
change (Z.to_nat 0) with 0%nat.
orewrite Z_to_nat_nonpos.
change (Z.of_nat 0%nat) with 0.
destruct l => //=.
rewrite Z.shiftr_0_r Z.add_nocarry_lxor? Z_land_dist.
replace (Z.land (2 ^ 8 * ZofList 8 l) 1) with 0.
rewrite Z.lxor_0_r //.
symmetry ; rewrite Z.land_comm.
1,2: apply Zland_pow => //=.
by apply Forall_cons_1 in Hl ; destruct Hl.
Qed.

Local Lemma getbit_repr_low l i :
  0 <= i->
  i / 8 < Zlength l ->
  Forall (fun x => 0 <= x < 2^8) l ->
  Mid.getbit i (ZofList 8 l) = Low.getbit i l.
Proof.
rewrite /Mid.getbit /Low.getbit.
move=> Hi Hli Hl.
rewrite Forall_Pos_bound; [|assumption].
have ->: (i <? 0 = false).
  by apply Z.ltb_ge.
have ->: Z.of_nat (Z.to_nat i) = i.
  by rewrite Z2Nat.id.
assert(0 <= i `div` 8).
  apply Z_div_pos ; omega.
assert(0 <= i `mod` 8).
  apply Z_mod_pos ; omega.
change 7 with (Z.ones 3).
orewrite Z.land_ones.
orewrite Z.shiftr_div_pow2.
orewrite Z.shiftr_div_pow2.
2: apply Z_mod_pos ; reflexivity.
orewrite Z.shiftr_div_pow2.
change (2^3) with 8.

apply Z2Nat.inj_lt in Hli.
rewrite Zlength_correct in Hli.
rewrite Nat2Z.id in Hli.
2: omega.
2: apply Zlength_pos.
rewrite (ZofList_nth_mod_div 8 _) ; try omega ; try assumption.
replace (Z.of_nat (Z.to_nat (i `div` 8))) with (i `div` 8).
2: rewrite Z2Nat.id ; try omega.
remember (ZofList 8 l) as a.
rewrite Zdiv_Zdiv.
rewrite -Z.pow_add_r ; try omega.
replace (8 * i `div` 8 + i `mod` 8) with i.
2: by apply Z_div_mod_eq.
2: by apply Z.pow_nonneg.
2: by apply Z.pow_nonneg.
rewrite -?Z.shiftr_div_pow2 //.
replace 1 with ((1 ≪ i) ≫ i).
2: rewrite Z.shiftr_shiftl_l //.
2: rewrite -Zminus_diag_reverse ; reflexivity.
rewrite -?Z.shiftr_land.
rewrite -Z.land_ones.
2: omega.
rewrite -Z.land_assoc.
have ->: (Z.land (Z.ones (8 * S (Z.to_nat (i `div` 8)))) (1 ≪ i) = 1 ≪ i) => //.
  have ->: (8 * S (Z.to_nat (i `div` 8)) = 8 * (1 + (i `div` 8))).
    rewrite -NPeano.Nat.add_1_l Nat2Z.inj_add ?Z2Nat.id //=.
rewrite Z.land_comm Z.land_ones; try omega.
rewrite Z.mod_small //.
split.
by apply Z.shiftl_nonneg.
rewrite Z.shiftl_mul_pow2 //.
rewrite Z.mul_1_l.
apply Z.pow_lt_mono_r; try omega.
rewrite -Zred_factor2 (Z_div_mod_eq i 8); try omega.
have ->: ((8 * i `div` 8 + i `mod` 8) `div` 8 = i `div` 8).
  by rewrite -(Z_div_mod_eq i 8).
rewrite Z.add_comm.
apply Zplus_lt_compat_r.
apply Z_mod_lt.
omega.
Qed.

Local Lemma getbit_repr_high : forall l i,
  0 <= i->
  i / 8 >= Zlength l ->
  Forall (fun x => 0 <= x < 2^8) l ->
  Mid.getbit i (ZofList 8 l) = Low.getbit i l.
Proof.
rewrite /Low.getbit /Mid.getbit.
move=> l i Hi Hli Hl.
rewrite Forall_Pos_bound; [|assumption].
have ->: i <? 0= false.
  by apply Z.ltb_ge.
have ->: Z.of_nat (Z.to_nat i) = i.
  by rewrite Z2Nat.id.
assert(0 <= i `div` 8).
  apply Z_div_pos ; omega.
assert(0 <= i `mod` 8).
  apply Z_mod_pos ; omega.
change 7 with (Z.ones 3).
orewrite Z.land_ones.
orewrite Z.shiftr_div_pow2.
orewrite Z.shiftr_div_pow2.
2: apply Z_mod_pos ; reflexivity.
orewrite Z.shiftr_div_pow2.
change (2^3) with 8.
replace (nth (Z.to_nat (i `div` 8)) l 0) with 0.
replace (ZofList 8 l `div` 2 ^ i) with 0.
reflexivity.
{
symmetry; apply Zdiv_small.
split.
apply ZofList_pos.
omega.
rewrite /ZList_pos.
eapply list.Forall_impl.
eassumption.
simpl ; intros ; omega.
assert(HZL: Zlength l = length l) by (rewrite Zlength_correct ; reflexivity).
assert(H80: 8 > 0) by omega.
assert (Hll := ZofList_n_nn_bound_Zlength 8 H80 l (length l) HZL Hl).
assert(2 ^ (8 * length l) <= 2 ^ i).
replace (length l) with (Z.to_nat (Zlength l)) by (rewrite Zlength_correct Nat2Z.id; reflexivity).
apply Z.pow_le_mono_r.
omega.
rewrite Z2Nat.id.
2: apply Zlength_pos.
clear Hll H80 H0 H Hl HZL.
apply Z.ge_le in Hli.
apply (Zmult_le_compat_r _ _ 8) in Hli.
2: omega.
rewrite Z.mul_comm.
assert(i `div` 8 * 8 <= i).
rewrite Z.mul_comm.
apply Z_mult_div_ge.
omega.
omega.
omega.
}
{
symmetry. apply nth_overflow.
replace (length l) with (Z.to_nat (Zlength l)).
apply Z2Nat.inj_le.
apply Zlength_pos.
assumption.
omega.
rewrite Zlength_correct Nat2Z.id ; reflexivity.
}
Qed.

Lemma getbit_repr : forall l i,
  Forall (fun x => 0 <= x < 2^8) l ->
  Mid.getbit i (ZofList 8 l) = Low.getbit i l.
Proof.
  intros.
  assert(Hi: i < 0 \/ 0 <= i) by omega.
  destruct Hi as [Hi|Hi].
  apply getbit_minus; assumption.
  assert(HZL: i / 8 < Zlength l \/ i / 8 >= Zlength l) by omega.
  destruct HZL as [HZL|HZL].
  apply getbit_repr_low ; assumption.
  apply getbit_repr_high ; assumption.
Qed.

Close Scope Z.