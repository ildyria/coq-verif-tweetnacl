(* r=(z[i>>3]>>(i&7))&1; *)

Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Mid.GetBit.
Require Import ssreflect.
Require Import stdpp.list.

Open Scope Z.

Definition getbit (i:Z) (l : list Z) := Z.land ((Z.shiftr (nth (Z.to_nat (Z.shiftr i 3)) l 0)  (Z.land i 7))) 1.

Lemma getbit_0_or_1 : forall i l,
  0 <= getbit i l <= 1.
Proof.
intros.
unfold getbit.
apply and_0_or_1.
Qed.

Lemma getbit_repr : forall l i,
  0 <= i->
  i / 8 < Zlength l ->
  Forall (fun x => 0 <= x < 2^8) l ->
  Zgetbit i (ZofList 8 l) = getbit i l.
Proof.
rewrite /getbit /Zgetbit.
move=> l i Hi Hli Hl.
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
2: apply Z_div_mod_eq ; omega.
2: apply Z.pow_nonneg; omega.
2: apply Z.pow_nonneg; omega.
rewrite -?Z.shiftr_div_pow2 ; try omega.
replace 1 with ((1 ≪ i) ≫ i).
2: rewrite Z.shiftr_shiftl_l ; try omega.
2: rewrite -Zminus_diag_reverse ; reflexivity.
rewrite -?Z.shiftr_land.
rewrite -Z.land_ones.
2: omega.
rewrite -Z.land_assoc.
replace (Z.land (Z.ones (8 * S (Z.to_nat (i `div` 8)))) (1 ≪ i)) with (1 ≪ i).
reflexivity.
replace (8 * S (Z.to_nat (i `div` 8))) with (8 * (1 + (i `div` 8))).
2: f_equal.
2: rewrite -NPeano.Nat.add_1_l Nat2Z.inj_add ?Z2Nat.id ; simpl ; omega.
rewrite Z.land_comm.
rewrite Z.land_ones ; try omega.
rewrite Z.mod_small.
reflexivity.
split.
apply Z.shiftl_nonneg ; omega.
rewrite Z.shiftl_mul_pow2; try omega.
rewrite Z.mul_1_l.
apply Z.pow_lt_mono_r; try omega.
rewrite -Zred_factor2.
rewrite (Z_div_mod_eq i 8); try omega.
replace ((8 * i `div` 8 + i `mod` 8) `div` 8) with (i `div` 8).
2: rewrite -(Z_div_mod_eq i 8); omega.
rewrite Z.add_comm.
apply Zplus_lt_compat_r.
apply Z_mod_lt.
omega.
Qed.

Close Scope Z.