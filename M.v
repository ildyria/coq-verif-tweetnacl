Require Export ScalarMult.
Require Export A.
Import ListNotations.
Require Export Tools.
Open Scope Z.

Fixpoint mult_1 (a b:list Z) : list Z := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: (ha ∘ qb) ⊕ (mult_1 qa (hb::qb))
end.

Definition mult_2 (a:list Z) : list Z := a  ⊕ (38 ∘ (tail 16 a)).

Definition mult_3 (a:list Z) : list Z := slice 16 a.

Definition M (a b:list Z) : list Z :=
  let m1 := mult_1 a b in
    let m2 := mult_2 m1 in
      mult_3 m2.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma mult1_correct_impl : forall (a b c: list Z), mult_1 a b = c -> (ℤ.lst a) * (ℤ.lst b) = ℤ.lst c.
Proof.
induction a, b ; intros c Hc.
- simpl in *; go.
- simpl in *; go.
- simpl in Hc.
  rewrite Z.mul_comm.
  go.
- rewrite! ZofList_cons.
  unfold mult_1 in Hc; fold mult_1 in Hc.
  rewrite <- Hc.
  rewrite ZofList_cons.
  rewrite ZsumList_correct.
  rewrite <- (IHa (z :: b) (mult_1 a0 (z :: b))) by go.
  rewrite ZofList_cons.
  rewrite ZscalarMult_correct.
  ring.
Qed.

Corollary mult1_correct : forall (a b: list Z), ℤ.lst mult_1 a b =  (ℤ.lst a) * (ℤ.lst b).
Proof.
intros a b.
symmetry.
erewrite mult1_correct_impl ; go.
Qed.

Lemma mult_2_correct : forall (l: list Z), (ℤ.lst mult_2 l) = (ℤ.lst l) + 38 * ℤ.lst tail 16 l.
Proof.
intros l.
unfold mult_2.
rewrite ZsumList_correct.
rewrite ZscalarMult_correct.
go.
Qed.

End Integer.

Lemma reduce_slice_GF:
  forall (l:list Z),
    ℤ.ℕ length l < 32 ->
    (ℤ16.lst mult_3 (mult_2 l)) :𝓖𝓕 = (ℤ16.lst l) :𝓖𝓕.
Proof.
intros l Hl.
unfold mult_3.
unfold mult_2.
rewrite ZofList_slice ; try omega.
rewrite ZsumList_correct.
rewrite ZscalarMult_correct.
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
  rewrite ZofList_nil.
  f_equal.
  ring.
}
{
  assert(Hlength: length (slice 16 (l ⊕ 38 ∘ tail 16 l)) = 16%nat).
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
  replace (16 * ℤ.ℕ 16) with 256 by go.
  assert(Hnul: (38 * (ℤ16.lst tail 16 l) - 2 ^ 256 * (ℤ16.lst tail 16 l)) :𝓖𝓕  = 0).
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

Lemma Zsucc16 : Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ (Z.succ 0))))))))))))))) = 16.
Proof.
compute ; reflexivity.
Qed.

Corollary mult_GF: forall a b, ℤ.ℕ length a = 16 -> ℤ.ℕ length b = 16 ->  (ℤ16.lst M a b) :𝓖𝓕 = (ℤ16.lst a) * (ℤ16.lst b) :𝓖𝓕.
Proof.
intros a b Hla Hlb.
unfold M.
rewrite reduce_slice_GF.
f_equal.
rewrite mult1_correct.
go.
rewrite <- Zlength_correct in *.
destruct a ; [inversion Hla|]. (* 0 *)
destruct a ; [inversion Hla|]. (* 1 *)
destruct a ; [inversion Hla|]. (* 2 *)
destruct a ; [inversion Hla|]. (* 3 *)
destruct a ; [inversion Hla|]. (* 4 *)
destruct a ; [inversion Hla|]. (* 5 *)
destruct a ; [inversion Hla|]. (* 6 *)
destruct a ; [inversion Hla|]. (* 7 *)
destruct a ; [inversion Hla|]. (* 8 *)
destruct a ; [inversion Hla|]. (* 9 *)
destruct a ; [inversion Hla|]. (* 10 *)
destruct a ; [inversion Hla|]. (* 11 *)
destruct a ; [inversion Hla|]. (* 12 *)
destruct a ; [inversion Hla|]. (* 13 *)
destruct a ; [inversion Hla|]. (* 14 *)
destruct a ; [inversion Hla|]. (* 15 *)
destruct a ; [inversion Hla|]. (* 16 *)
- destruct b ; [inversion Hlb|]. (* 0 *)
destruct b ; [inversion Hlb|]. (* 1 *)
destruct b ; [inversion Hlb|]. (* 2 *)
destruct b ; [inversion Hlb|]. (* 3 *)
destruct b ; [inversion Hlb|]. (* 4 *)
destruct b ; [inversion Hlb|]. (* 5 *)
destruct b ; [inversion Hlb|]. (* 6 *)
destruct b ; [inversion Hlb|]. (* 7 *)
destruct b ; [inversion Hlb|]. (* 8 *)
destruct b ; [inversion Hlb|]. (* 9 *)
destruct b ; [inversion Hlb|]. (* 10 *)
destruct b ; [inversion Hlb|]. (* 11 *)
destruct b ; [inversion Hlb|]. (* 12 *)
destruct b ; [inversion Hlb|]. (* 13 *)
destruct b ; [inversion Hlb|]. (* 14 *)
destruct b ; [inversion Hlb|]. (* 15 *)
destruct b. (* 16 *)
+ simpl.
  rewrite! Zlength_cons.
  rewrite Zlength_nil.
  compute. (* LOL ! Thx God ! *)
  reflexivity.
+ clear Hla. exfalso. (* lets get a bit of visibility *)
  rewrite! Zlength_cons in Hlb.
  rewrite <- Zsucc16 in Hlb ; 
  repeat (rewrite Z.succ_inj_wd in Hlb).
  rewrite Zlength_correct in Hlb.
  rewrite <- Nat2Z.inj_succ in Hlb.
  rewrite <- Nat2Z.inj_0 in Hlb.
  rewrite Nat2Z.inj_iff in Hlb.
  inversion Hlb.
- clear Hlb. exfalso. (* lets get a bit of visibility *)
  rewrite! Zlength_cons in Hla.
  rewrite <- Zsucc16 in Hla ;
  repeat (rewrite Z.succ_inj_wd in Hla).
  rewrite Zlength_correct in Hla.
  rewrite <- Nat2Z.inj_succ in Hla.
  rewrite <- Nat2Z.inj_0 in Hla.
  rewrite Nat2Z.inj_iff in Hla.
  inversion Hla.
Qed.

