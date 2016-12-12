Require Export ScalarMult.
Require Export Forall_ZopList.
Require Export MultBounds.
Require Export A.
Import ListNotations.
Require Export Tools.
Require Export Zlength.
Require Export Calc_lib.
Require Export TrippleRel.
Open Scope Z.

Lemma ZscalarMult_bound_const: forall (m2 n2 o p a: Z) (b: list Z),
  0 <= a ->
  Forall (fun x => m2 <= x <= n2) b -> 
  o = a * m2 ->
  p = a * n2 ->
  Forall (fun x => o <= x <= p) (a ∘ b).
Proof.
  introv Ha Hb Ho Hp.
  rewrite ZscalarMult_eq_ZunopList.
  eapply (Forall_ZunopList _ (fun x : ℤ => a = x) (fun x : ℤ => m2 <= x <= n2)) ; go.
Qed.

Lemma ZscalarMult_bound_inter: forall (m1 n1 m2 n2 o p a: Z) (b: list Z),
  (fun x => m1 <= x <= n1) a ->
  Forall (fun x => m2 <= x <= n2) b -> 
  o = min_prod m1 n1 m2 n2 ->
  p = max_prod m1 n1 m2 n2 ->
  Forall (fun x => o <= x <= p) (a ∘ b).
Proof.
  introv Ha Hb Ho Hp.
  rewrite ZscalarMult_eq_ZunopList.
  eapply (Forall_ZunopList _ (fun x : ℤ => m1 <= x <= n1) (fun x : ℤ => m2 <= x <= n2)) ; try assumption.
  subst o p.
  apply Mult_interval_correct_min_max_le ; auto.
Qed.

Fixpoint mult_1 (a b:list Z) : list Z := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: (ha ∘ qb) ⊕ (mult_1 qa (hb::qb))
end.

Lemma mult_1_cons: forall ha qa hb qb, mult_1 (ha :: qa) (hb :: qb) = ha * hb :: (ha ∘ qb) ⊕ (mult_1 qa (hb::qb)).
Proof. intros; auto. Qed.

Lemma mult1_com: forall (b a:list Z), mult_1 a b = mult_1 b a.
Proof.
induction b as [| hb qb IHb].
destruct a ; auto.
induction a ; auto.
simpl.
f_equal.
apply Z.mul_comm.
rewrite IHa.
destruct a0.
simpl.
rewrite  <- IHb.
simpl.
flatten ; repeat rewrite ZsumList_nil_r ; go.
rewrite <- IHb.
simpl.
flatten.
flatten Eq.
repeat rewrite ZsumList_nil_r ; go.
flatten Eq.
rewrite <- IHb.
simpl.
f_equal.
omega.
rewrite <- ZsumList_assoc.
rewrite <- ZsumList_assoc.
f_equal.
rewrite ZsumList_comm.
reflexivity.
Qed.

Lemma mult_1_bound_le_len : forall (a b: list Z) (m1 n1 m2 n2 m3 n3: Z) ,
  (length a <= length b)%nat ->
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  Forall (fun x => m2 <= x <= n2) b ->
  m3 = Zmin (Zlength a) (Zlength b) * min_prod m1 n1 m2 n2 -> 
  n3 = Zmin (Zlength a) (Zlength b) * max_prod m1 n1 m2 n2 ->
  Forall (fun x => m3 <= x <= n3) (mult_1 a b).
Proof.
  induction a ; introv Hl Hmn1 Hmn2 Ha Hb Hm3 Hn3.
  - go.
  - destruct b.
    simpl ; go.
    simpl.
    apply Forall_cons.
    + inv Ha.
      inv Hb.
      assert(Hstrict: min_prod m1 n1 m2 n2 <= a * z <= max_prod m1 n1 m2 n2).
        apply Mult_interval_correct_min_max_le ; auto.
      assert( 1 <= Z.min (Zlength (a :: a0)) (Zlength (z :: b))).
        apply Z.min_glb ; rewrite Zlength_cons.
        assert(0 <= Zlength a0) by apply Zlength_pos ;  omega.
        assert(0 <= Zlength b) by apply Zlength_pos ;  omega.
      eapply le_le_trans.
      eauto.
      apply le_mul_neg_le ; auto.
      apply min_prod_neg_le ; auto.
      apply le_mul_pos_le ; auto.
      apply max_prod_pos_le ; auto.
    + subst m3 n3.
      repeat rewrite Zlength_cons.
      rewrite <- Z.succ_min_distr.
      replace (Z.succ (Z.min (Zlength a0) (Zlength b))) with (1 + Z.min (Zlength a0) (Zlength b)) by omega.
      replace (Z.succ (Z.min (Zlength a0) (Zlength b))) with (1 + Z.min (Zlength a0) (Zlength b)) by omega.
      assert(Htemp: 
      (1 + Z.min (Zlength a0) (Zlength b)) * min_prod m1 n1 m2 n2 = min_prod m1 n1 m2 n2 + min_prod m1 n1 m2 n2 * Z.min (Zlength a0) (Zlength b)).
      rewrite Z.mul_comm ; rewrite <- Zred_factor2 ; auto.
      rewrite Htemp ; clear Htemp.
      assert(Htemp: 
      (1 + Z.min (Zlength a0) (Zlength b)) * max_prod m1 n1 m2 n2 = max_prod m1 n1 m2 n2 + max_prod m1 n1 m2 n2 * Z.min (Zlength a0) (Zlength b)).
      rewrite Z.mul_comm ; rewrite <- Zred_factor2 ; auto.
      rewrite Htemp ; clear Htemp.
      eapply ZsumList_bound_le.
      split.
      apply min_prod_neg_le ; auto.
      apply max_prod_pos_le ; auto.
      assert(0 <= Z.min (Zlength a0) (Zlength b)). 
        unfold Z.min. flatten; apply Zlength_pos ;  omega.
      split.
      apply Z.mul_nonpos_nonneg ; auto.
      apply min_prod_neg_le ; auto.
      apply Z.mul_nonneg_nonneg ; auto.
      apply max_prod_pos_le ; auto.
      eapply ZscalarMult_bound_inter; eauto.
      inv Ha ; auto.
      inv Hb ; auto.
      eapply IHa ; auto.
      repeat rewrite length_cons in Hl ; rewrite length_cons ; inv Hl;  omega.
      eapply Hmn1.
      eapply Hmn2.
      inv Ha ; auto.
      auto.
      rewrite Z.mul_comm.
      f_equal.
      rewrite Z.min_l.
      rewrite Z.min_l.
      reflexivity.
      repeat rewrite Zlength_correct ; apply inj_le ;
      repeat rewrite length_cons in Hl ; rewrite length_cons ; inv Hl;  omega.
      repeat rewrite Zlength_correct ; apply inj_le ;
      repeat rewrite length_cons in Hl ; inv Hl;  omega.
      rewrite Z.mul_comm.
      f_equal.
      rewrite Z.min_l.
      rewrite Z.min_l.
      reflexivity.
      repeat rewrite Zlength_correct ; apply inj_le ;
      repeat rewrite length_cons in Hl ; rewrite length_cons ; inv Hl;  omega.
      repeat rewrite Zlength_correct ; apply inj_le ;
      repeat rewrite length_cons in Hl ; inv Hl;  omega.
Qed.

Lemma mult_1_bound_le : forall (a b: list Z) (m1 n1 m2 n2 m3 n3: Z) ,
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  Forall (fun x => m2 <= x <= n2) b ->
  m3 = Zmin (Zlength a) (Zlength b) * min_prod m1 n1 m2 n2 -> 
  n3 = Zmin (Zlength a) (Zlength b) * max_prod m1 n1 m2 n2 ->
  Forall (fun x => m3 <= x <= n3) (mult_1 a b).
Proof.
  introv Hmn1 Hmn2 Ha H2 Hm3 Hn3.
  assert(HL: (length a <= length b)%nat \/ (length b <= length a)%nat) by omega.
  destruct HL.
  eapply mult_1_bound_le_len ; [|eapply Hmn1|eapply Hmn2| | | |] ; eauto.
  rewrite mult1_com.
  eapply mult_1_bound_le_len ; [|eapply Hmn2|eapply Hmn1| | | |] ; eauto ; 
  subst m3; subst n3 ;
  unfold min_prod;
  unfold max_prod;
  f_equal ; try apply Z.min_comm ; try apply Z.max_comm;
  f_equal ; [|rewrite Z.min_comm| |rewrite Z.max_comm];
  f_equal ; try apply Z.mul_comm.
Qed.

Definition mult_2 (a:list Z) : list Z := a  ⊕ (38 ∘ (tail 16 a)).

Lemma mult_2_bound_le: forall (m1 n1 m2 n2: Z) (a: list Z),
  m2 = m1 + 38 * m1 ->
  n2 = n1 + 38 * n1 ->
  (fun x => m1 <= x <= n1) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  Forall (fun x => m2 <= x <= n2) (mult_2 a).
Proof.
  intros m1 n1 m2 n2 a Ha H0 Hm2 Hn2.
  unfold mult_2.
  subst m2 n2.
  eapply ZsumList_bound_le ; simpl in Hm2 ; try omega ; auto.
  eapply ZscalarMult_bound_const ; go.
  apply Forall_tail ; eauto.
Qed.

Definition mult_3 (a:list Z) : list Z := slice 16 a.

Lemma mult_3_bound_le : forall m1 n1 a,
  Forall (fun x => m1 <= x <= n1) a ->
    Forall (fun x => m1 <= x <= n1) (mult_3 a).
Proof.
  intros.
  unfold mult_3.
  apply Forall_slice.
  assumption.
Qed.

Definition M (a b:list Z) : list Z :=
  let m1 := mult_1 a b in
    let m2 := mult_2 m1 in
      mult_3 m2.

Lemma mult_bound_le: forall (m1 n1 m2 n2: Z) (a b: list Z),
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  Forall (fun x => m2 <= x <= n2) b ->
  Forall (fun x => 39 * Z.min (Zlength a) (Zlength b) * min_prod m1 n1 m2 n2 <= x <= 39 * Z.min (Zlength a) (Zlength b) * max_prod m1 n1 m2 n2) (M a b).
Proof.
  introv Hmn1 Hmn2 Ha Hb.
  unfold M.
  apply mult_3_bound_le.
  eapply (mult_2_bound_le (Z.min (Zlength a) (Zlength b) * min_prod m1 n1 m2 n2)  (Z.min (Zlength a) (Zlength b) * max_prod m1 n1 m2 n2)).
  change 39 with (1 + 38).
  rewrite Zmult_assoc_reverse.
  apply Zred_factor7.
  change 39 with (1 + 38).
  rewrite Zmult_assoc_reverse.
  apply Zred_factor7.
  assert(0 <= Z.min (Zlength a) (Zlength b)). 
    unfold Z.min; flatten; apply Zlength_pos ;  omega.
  split.
  rewrite Z.mul_comm.
  apply Z.mul_nonpos_nonneg ; auto.
  apply min_prod_neg_le ; auto.
  apply Z.mul_nonneg_nonneg ; auto.
  apply max_prod_pos_le ; auto.
  eapply mult_1_bound_le; [eapply Hmn1|eapply Hmn2| | | | ] ; eauto.
Qed.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma mult1_correct_impl : forall (a b c: list Z),
  mult_1 a b = c -> (ℤ.lst a) * (ℤ.lst b) = ℤ.lst c.
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

Corollary mult1_correct : forall (a b: list Z),
  ℤ.lst mult_1 a b =  (ℤ.lst a) * (ℤ.lst b).
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
Proof. compute ; reflexivity. Qed.

Corollary mult_GF: forall a b, ℤ.ℕ length a = 16 -> ℤ.ℕ length b = 16 ->  (ℤ16.lst M a b) :𝓖𝓕 = (ℤ16.lst a) * (ℤ16.lst b) :𝓖𝓕.
Proof.
  intros a b Hla Hlb.
  unfold M.
  rewrite reduce_slice_GF.
  f_equal.
  rewrite mult1_correct.
  go.
  rewrite <- Zlength_correct in *.
  do 16 (destruct a ; tryfalse).
  destruct a.
  - do 16 (destruct b ; tryfalse).
    destruct b.
    + go.
    + clear Hla. exfalso. (* lets get a bit of visibility *)
      repeat rewrite Zlength_cons in Hlb.
      rewrite <- Zsucc16 in Hlb ; 
      repeat (rewrite Z.succ_inj_wd in Hlb).
      rewrite Zlength_correct in Hlb.
      rewrite <- Nat2Z.inj_succ in Hlb.
      rewrite <- Nat2Z.inj_0 in Hlb.
      rewrite Nat2Z.inj_iff in Hlb.
      inversion Hlb.
  - clear Hlb. exfalso. (* lets get a bit of visibility *)
    repeat rewrite Zlength_cons in Hla.
    rewrite <- Zsucc16 in Hla ;
    repeat (rewrite Z.succ_inj_wd in Hla).
    rewrite Zlength_correct in Hla.
    rewrite <- Nat2Z.inj_succ in Hla.
    rewrite <- Nat2Z.inj_0 in Hla.
    rewrite Nat2Z.inj_iff in Hla.
    inversion Hla.
Qed.

