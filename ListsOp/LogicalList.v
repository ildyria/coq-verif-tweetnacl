Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Export ListsOp.ZofList.
From Tweetnacl Require Export ListsOp.Forall_ZofList.
From Tweetnacl Require Import ListsOp.Zipp.

Definition Zlist_and a b := Zipp (Z.land) a b.
Definition Zlist_or a b := Zipp (Z.lor) a b.

Open Scope Z.

Lemma Zlist_and_ZofList : forall n a b,
  0 < n ->
  Forall (fun x => 0 <= x < 2^n) a ->
  Forall (fun x => 0 <= x < 2^n) b ->
  Z.land (ZofList n a) (ZofList n b) = ZofList n (Zlist_and a b).
Proof.
  intros n a b Hn; gen a b.
  induction a as [| a la IHa];
  intros [|b lb] => Ha Hb.
  reflexivity.
  simpl.
  replace (ZofList n (map (Z.land 0) lb)) with 0.
  omega.
  clear b Ha Hb.
  induction lb as [| b lb IHlb].
  reflexivity.
  simpl.
  rewrite -IHlb.
  omega.
  simpl.
  rewrite ?Z.land_0_r.
  replace (ZofList n (map (λ x : ℤ, Z.land x 0) la)) with 0.
  omega.
  clear a IHa Ha Hb.
  induction la as [| a la IHla].
  reflexivity.
  simpl.
  rewrite Z.land_0_r -IHla.
  omega.
  simpl.
  apply Forall_cons in Ha.
  apply Forall_cons in Hb.
  destruct Ha as [Ha Hla].
  destruct Hb as [Hb Hlb].
  orewrite Zxor_add.
  rewrite -IHa ; try assumption.
  orewrite Zxor_add.
  orewrite Zxor_add.
  2: apply Z_land_bound; omega.
  rewrite Z_land_dist.
  rewrite (Z.land_comm a).
  rewrite Z_land_dist.
  rewrite -(Z.land_comm a).
  rewrite (Z.land_comm (2 ^ n * ZofList n la)).
  rewrite Z_land_dist.
  replace (Z.land b (2 ^ n * ZofList n la)) with 0.
  replace (Z.land (2 ^ n * ZofList n lb) a) with 0.
  rewrite Z.lxor_0_l.
  rewrite Z.lxor_0_r.
  rewrite Z.mul_comm.
  rewrite -Z.shiftl_mul_pow2 ; try omega.
  rewrite Z.mul_comm.
  rewrite -Z.shiftl_mul_pow2 ; try omega.
  rewrite -Z.shiftl_land.
  rewrite Z.mul_comm.
  rewrite -Z.shiftl_mul_pow2 ; try omega.
  f_equal.
  rewrite Z.land_comm.
  reflexivity.
  rewrite Z.land_comm.
  rewrite Z_land_null ; omega.
  rewrite Z_land_null ; omega.
Qed.

Lemma Forall_Zlist_and: forall n a b,
  0 < n ->
  Forall (fun x => 0 <= x < 2^n) a ->
  Forall (fun x => 0 <= x < 2^n) b ->
  Forall (fun x => 0 <= x < 2^n) (Zlist_and a b).
Proof.
  intros n a b Hn ; gen a b.
  induction a as [| a la IHa] ; induction b as [|b lb IHb] => Ha Hb.
  unfold Zlist_and; simpl ; by apply Forall_nil.
  replace (Zlist_and [] (b :: lb)) with (0 :: Zlist_and [] (lb)).
  2: rewrite /Zlist_and; simpl ; flatten ; reflexivity.
  apply Forall_cons_2.
  split; try omega.
  apply Z.gt_lt.
  apply pown0.
  omega.
  apply Forall_cons in Hb; destruct Hb.
  apply IHb; try assumption.
  replace (Zlist_and (a :: la) []) with (0 :: Zlist_and la []).
  2: rewrite /Zlist_and ; simpl ; rewrite Z.land_0_r ; destruct la ; reflexivity.
  apply Forall_cons_2.
  split; try omega.
  apply Z.gt_lt.
  apply pown0.
  omega.
  apply Forall_cons in Ha; destruct Ha.
  apply IHa; try assumption.
  apply Forall_cons in Ha; destruct Ha.
  apply Forall_cons in Hb; destruct Hb.
  replace (Zlist_and (a :: la) (b :: lb)) with ((Z.land a b) :: Zlist_and la lb).
  2: rewrite /Zlist_and ; simpl ; reflexivity.
  apply Forall_cons_2.
  apply Z_land_bound ; omega.
  apply IHa; try assumption.
Qed.

Lemma Zlist_or_ZofList : forall n a b,
  0 < n ->
  Forall (fun x => 0 <= x < 2^n) a ->
  Forall (fun x => 0 <= x < 2^n) b ->
  Z.lor (ZofList n a) (ZofList n b) = ZofList n (Zlist_or a b).
Proof.
  intros n a b Hn; gen a b.
  induction a as [| a la IHa];
  intros [|b lb] => Ha Hb.
  reflexivity.
  simpl.
  replace (map (Z.lor 0) lb) with lb.
  omega.
  clear b Ha Hb.
  induction lb as [| b lb IHlb].
  reflexivity.
  simpl.
  rewrite -IHlb.
  reflexivity.
  simpl.
  rewrite ?Z.lor_0_r.
  replace (map (λ x : ℤ, Z.lor x 0) la) with la.
  omega.
  clear a IHa Ha Hb.
  induction la as [| a la IHla].
  reflexivity.
  simpl.
  rewrite Z.lor_0_r -IHla.
  reflexivity.
  simpl.
  apply Forall_cons in Ha.
  apply Forall_cons in Hb.
  destruct Ha as [Ha Hla].
  destruct Hb as [Hb Hlb].
  orewrite Zor_add.
  rewrite -IHa ; try assumption.
  orewrite Zor_add.
  orewrite Zor_add.
  2: apply Z_lor_bound; omega.
  rewrite -Z.lor_assoc.
  rewrite -Z.lor_assoc.
  f_equal.
  rewrite Z.lor_comm.
  rewrite -Z.lor_assoc.
  f_equal.
  rewrite Z.mul_comm.
  rewrite -Z.shiftl_mul_pow2 ; try omega.
  rewrite Z.mul_comm.
  rewrite -Z.shiftl_mul_pow2 ; try omega.
  rewrite Z.mul_comm.
  rewrite -Z.shiftl_mul_pow2 ; try omega.
  rewrite -Z.shiftl_lor.
  f_equal.
  rewrite Z.lor_comm.
  reflexivity.
Qed.

Close Scope Z.