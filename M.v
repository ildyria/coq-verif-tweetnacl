Require Export SumList.
Require Export ToFF.
Require Export ScalarMult.
Require Export A.
Import ListNotations.
Require Export Tools.
Open Scope Z.

Fixpoint mult_1 a b := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: ZsumList (ZscalarMult ha qb) (mult_1 qa (hb::qb))
end.

(*
Fixpoint mult_1' a b := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: ZsumList (ZsumList (scalarMult ha qb) (scalarMult hb qa))
 (match mult_1' qa qb with 
  | [] => []
  | l => 0 :: l
  end)
end.

Lemma mult_1'_comm : forall a b, mult_1' a b = mult_1' b a.
Proof.
induction a,b ; go.
unfold mult_1' ; fold mult_1'.
f_equal ; go.
rewrite IHa.
f_equal.
rewrite sum_list_comm ; go.
Qed.

Fixpoint List_is_eq a b : bool := match a, b with
| [], [] => true
| h1 :: q1, h2 :: q2 => andb (Zeq_bool h1 h2) (List_is_eq q1 q2)
| _,_ => false
end.

Compute List_is_eq (mult_1' [1;1;1;1;1;1;1;1;1] []) (mult_1 [1;1;1;1;1;1;1;1;1] []).
Compute List_is_eq (mult_1' [0] [0]) (mult_1 [0] [0]).
*)

Definition mult_2 a := ZsumList a (ZscalarMult 38 (tail 16 a)).

Definition mult_3 (a:list Z) : list Z := slice 16 a.

Definition M a b :=
  let m1 := mult_1 a b in
    let m2 := mult_2 m1 in
      mult_3 m2.

Lemma MultToFF' : forall n a b c, mult_1 a b = c -> ToFF n a * ToFF n b = ToFF n c.
Proof.
intro n ; induction a, b ; intros c Hc.
- simpl in *; go.
- simpl in *; go.
- simpl in Hc.
  rewrite Z.mul_comm.
  go.
- rewrite! ToFF_cons.
  unfold mult_1 in Hc; fold mult_1 in Hc.
  rewrite <- Hc.
  rewrite ToFF_cons.
  rewrite ZsumListToFF2.
  rewrite <- (IHa (z :: b) (mult_1 a0 (z :: b))) by go.
  rewrite ToFF_cons.
  rewrite ZscalarMultToFF.
  ring.
Qed.

Lemma mult_2_ToFF : forall n l, ToFF n (mult_2 l) = ToFF n l + 38 * ToFF n (tail (16%nat) l).
Proof.
intros n l.
unfold mult_2.
rewrite ZsumListToFF2.
rewrite ZscalarMultToFF.
go.
Qed.

Lemma reduce_slice_ToFF:
  forall l,
    Z.of_nat (length l) < 32 ->
    (ToFF 16 (mult_3 (mult_2 l))) mod (Z.pow 2 255 - 19) = (ToFF 16 l) mod (Z.pow 2 255 - 19).
Proof.
intros l Hl.
unfold mult_3.
unfold mult_2.
rewrite ToFF_slice ; try omega.
rewrite ZsumListToFF2.
rewrite ZscalarMultToFF.
assert(Hlength: (length l <= 16 \/ length l > 16)%nat) by omega.
destruct Hlength.
{
  assert(Ht: tail 16 l = []).
    apply tail_length_le ; go.
  assert(Hs: slice 16 l = l).
    apply slice_length_le ; go.
  rewrite! Ht.
  rewrite! ZscalarMultnil.
  rewrite ZsumList_nil_r.
  rewrite Ht.
  rewrite Hs.
  rewrite ToFF_nil.
  f_equal.
  ring.
}
{
  assert(Hlength: length (slice 16 (ZsumList l (ZscalarMult 38 (tail 16 l)))) = 16%nat).
    rewrite slice_length_min.
    rewrite ZsumList_length_max.
    rewrite ZscalarMult_length.
    rewrite tail_length_eq_minus ; go.
    rewrite Max.max_l ; go.
    rewrite Min.min_l ; go.
  rewrite Hlength ; clear Hlength.
  rewrite ZsumList_tail.
  rewrite ZscalarMult_tail.
  assert(Htailtail: tail 16 (tail 16 l) = []).
    apply tail_length_le.
    rewrite tail_length_eq_minus ; go.
  rewrite Htailtail; clear Htailtail.
  rewrite ZscalarMultnil.
  rewrite ZsumList_nil_r.
  replace (16 * Z.of_nat 16) with 256 by go.
  assert(Hnul: (38 * ToFF 16 (tail 16 l) - 2 ^ 256 * ToFF 16 (tail 16 l)) mod (2 ^ 255 - 19) = 0).
    rewrite <- Zmult_minus_distr_r.
    rewrite Zmult_mod.
    replace ((38 - 2 ^ 256) mod (2 ^ 255 - 19)) with 0; compute ; reflexivity.
  rewrite <- Z.add_sub_assoc.
  rewrite <- Zplus_mod_idemp_r.
  rewrite Hnul ; clear Hnul.
  rewrite <- Zplus_0_r_reverse.
  reflexivity.
}
Qed.
