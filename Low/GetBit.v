(* r=(z[i>>3]>>(i&7))&1; *)

Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import ssreflect.
Require Import stdpp.prelude.

Open Scope Z.

Definition getbit (i:Z) (l : list Z) := Z.land ((Z.shiftr (nth (Z.to_nat (Z.shiftr i 3)) l 0)  (Z.land i 7))) 1.

Lemma and_0_or_1 : forall a , 0 <= Z.land a 1 <= 1.
Proof.
intros.
induction a ; try destruct p ; simpl ; flatten; go.
Qed.

Lemma getbit_0_or_1 : forall i l,
  0 <= getbit i l <= 1.
Proof.
intros.
unfold getbit.
apply and_0_or_1.
Qed.

Lemma getbit_repr : forall l i,
  0 <= i->
  i / 8 <= Zlength l ->
  Forall (fun x => 0 <= x < 2^8) l ->
  Z.land (Z.shiftr (ZofList 8 l) i) 1 = getbit i l.
Proof.
rewrite /getbit.
move=> l i Hi Hli Hl.
change 7 with (Z.ones 3).
orewrite Z.land_ones.
orewrite Z.shiftr_div_pow2.
orewrite Z.shiftr_div_pow2.
2: apply Z_mod_pos ; reflexivity.
(* orewrite Z.shiftr_div_pow2. *)
rewrite -(ZofList_take_nth_drop 8 _ l (Z.to_nat (i ≫ 3))) ; try omega.
rewrite Zlength_correct.
rewrite firstn_length_le.

Focus 2.
orewrite Z.shiftr_div_pow2.
change (2^3) with 8.
apply Z2Nat.inj_le in Hli.
rewrite Zlength_correct in Hli.
by rewrite Nat2Z.id in Hli.
2: apply Zlength_pos.
apply Z_div_pos ; omega.

Admitted.
