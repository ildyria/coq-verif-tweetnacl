Require Export ZofList.
Require Export Reduce.
Import ListNotations.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.


Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Fixpoint Carrying (a:Z) (l:list Z) : list Z := match a,l with 
| 0,[] => []
| a,[] => [a]
| a,h :: q => getResidue n (a + h) :: Carrying (getCarry n (a + h)) q
end.

Fixpoint Carrying_n (p:nat) (a:Z) (l:list Z) : list Z := match p,a,l with 
| _,  0,[]     => []
| _,  a,[]     => [a]
| 0%nat,  a,h::q   => (a + h) :: q
| S p,a,h :: q => getResidue n (a + h) :: Carrying_n p (getCarry n (a + h)) q
end.

Lemma Carry_n_step: forall m a h q, Carrying_n (S m) a (h :: q) = getResidue n (a + h) :: Carrying_n m (getCarry n (a + h)) q.
Proof. intros; simpl ; flatten. Qed.

Lemma Carrying_n_eq: forall l (m:nat) a, m = length l -> Carrying_n m a l = Carrying a l.
Proof.
  induction l as [|h q IHl]; intros m a Hm; go.
  destruct m.
  inv Hm.
  simpl in *.
  inversion Hm.
  flatten ; f_equal ; go.
Qed.

Lemma Carry_n_step_0 : forall h q a, Carrying_n 0 a (h :: q) = (a + h) :: q.
Proof. intros ; simpl; flatten. Qed.

Lemma Carrying_n_length: forall l (m:nat) a, (m < length l)%nat -> length (Carrying_n m a l) = length l.
Proof. induction l as [|h q IHl]; intros [] a Hm; simpl ; flatten ; go. Qed.


Lemma CarryPreserveConst : forall l a , a + (ℤ.lst l) = ℤ.lst Carrying a l.
Proof.
  induction l as [| h q IHl].
  intro a ; destruct a ; assert(Hn0: 2 ^ n * 0 = 0) by (symmetry ; apply Zmult_0_r_reverse) ; simpl ; try rewrite Hn0 ; go.
  intro a ; unfold Carrying ; fold Carrying.
  flatten ;
  unfold ZofList ; fold ZofList ; rewrite <- IHl ;
  rewrite <- Zplus_assoc_reverse ; 
  rewrite <- Zred_factor4 ;
  rewrite <- Zplus_assoc_reverse ;
  rewrite residuteCarry ;
  go.
Qed.

Lemma CarrynPreserveConst : forall m l a , a + (ℤ.lst l)  = ℤ.lst Carrying_n m a l.
Proof.
  assert(Hn0: 2 ^ n * 0 = 0) by (symmetry ; apply Zmult_0_r_reverse).
  induction m ; intros l a.
  - simpl ; flatten ; try rewrite <- ZofList_add ; go.
  - simpl ; flatten ; go ;
    rewrite! ZofList_cons ;
    rewrite <- IHm ; 
    rewrite <- Zplus_assoc_reverse ; 
    rewrite <- Zred_factor4 ;
    rewrite <- Zplus_assoc_reverse ;
    rewrite residuteCarry ; go.
Qed.

Corollary CarryPreserve : forall l, ℤ.lst l = ℤ.lst Carrying 0 l.
Proof.
  intros.
  symmetry.
  rewrite Zplus_0_r_reverse.
  symmetry.
  rewrite Z.add_comm.
  apply CarryPreserveConst.
Qed.

Corollary CarrynPreserve : forall m l, ℤ.lst l = ℤ.lst Carrying_n m 0 l.
Proof.
  intros.
  symmetry.
  rewrite Zplus_0_r_reverse.
  symmetry.
  rewrite Z.add_comm.
  apply CarrynPreserveConst.
Qed.

End Integer.

Definition backCarry (l:list Z) : (list Z) := 
  match l with
  | [] => []
  | h :: q => let v := nth 15 l 0 in
              (h + 38 * getCarry 16 v) :: slice 14 q ++ [getResidue 16 v]
  end.

Lemma backCarry_ToFF_25519 : forall l, (length l <= 16)%nat -> (ℤ16.lst l) :𝓖𝓕  = ((ℤ16.lst backCarry l) :𝓖𝓕).
Proof.
  destruct l as [| h l]; intro Hlength.
  - go.
  - unfold backCarry.
    repeat rewrite ZofList_cons.
    rewrite ZofList_app ; try omega.
    apply le_lt_eq_dec in Hlength.
    destruct Hlength.
    + rename l0 into H.
      rewrite nth_overflow by omega.
      simpl in H.
      apply lt_S_n in H.
      rewrite slice_length_le by omega.
      rewrite getResidue_0.
      rewrite getCarry_0.
      rewrite ZofList_cons_0.
      f_equal.
      ring.
    + rename e into H.
      repeat (destruct l ; tryfalse).
      clear H.
      unfold nth.
      unfold slice.
      change ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] ++ [ z13]).
      rewrite ZofList_app ; try omega.
      unfold length.
      repeat rewrite ZofList_cons_0.
      rewrite <- Zred_factor4.
      rewrite <- Zred_factor4.
      rewrite Zplus_assoc_reverse.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      symmetry.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      f_equal.
      f_equal.
      rewrite Z.add_shuffle3.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      symmetry.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      f_equal.
      f_equal.
      rewrite <- Z.add_mod_idemp_l by (compute ; omega).
      symmetry.
      rewrite Zmult_mod.
      rewrite <- t2256is38.
      rewrite <- Zmult_mod.
      rewrite Z.add_mod_idemp_l by (compute ; omega).
      change 256 with (16 + 16 * 15).
      rewrite Z.pow_add_r by omega.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_mod.
      f_equal.
      f_equal.
      change (2 ^ (16 * 15)) with (2 ^ (16 * 14) * 2 ^ 16).
      change (ℤ.ℕ 14) with 14.
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod.
      f_equal.
      f_equal.
      rewrite Z.add_comm.
      rewrite residuteCarry ; go.
Qed.

Definition car25519 (l:list Z) : list Z := backCarry (Carrying_n 16 15 0 l).

Lemma car25519_ToFF_25519 : forall l, (length l = 16)%nat -> (ℤ16.lst l) :𝓖𝓕  = (ℤ16.lst car25519 l) :𝓖𝓕.
Proof.
  intros l Hlength.
  unfold car25519.
  erewrite <- backCarry_ToFF_25519.
  rewrite <- CarrynPreserve.
  go.
  go.
  rewrite Carrying_n_length ; go.
Qed.

Lemma car25519_bound : forall i l, (length l = 16)%nat -> (i <> 0)%nat -> nth i (car25519 l) 0 < 2 ^ 16.
Proof.
  destruct i ; intros l H Hi ; [false|].
  apply destruct_length_16 in H.
  do 16 destruct H.
  unfold car25519.
  unfold backCarry.
  flatten. symmetry ; reflexivity.
  rewrite nth_cons.
  subst l.
  repeat rewrite Carry_n_step in Eq.
  rewrite Carry_n_step_0 in Eq.
  repeat (destruct l0 ; tryfalse).
  repeat rewrite ListSame in Eq.
  jauto_set.
  clear Hi H15.
  (* destruct the big /\ construction *)
  assert(Hi: (i < 14 \/ i = 14 \/ i > 14)%nat) by omega.
  (* case analisys on i: in slice, last elem or outside *)
  case Hi ; intro Hi_temp ; clear Hi ; rename Hi_temp into Hi.
  (* IN *)
  {
    rewrite app_nth1 ; unfold slice ; auto.
    simpl ; flatten ; subst ; try (apply getResidue_bounds ; omega).
    symmetry ; reflexivity.
    symmetry ; reflexivity.
  }
  case Hi ; intro Hi_temp ; clear Hi ; rename Hi_temp into Hi.
  {
    subst i.
    unfold slice.
    (* main goal *)
    - rewrite app_nth2.
    simpl.
    apply getResidue_bounds ; omega.
    (* goals generated by change *)
    compute ; omega.
  }
  { rewrite nth_overflow.
    symmetry ; reflexivity.
    rewrite app_length.
    unfold slice.
    compute.
    omega.
  }
Qed.

(*
    Proof could be smaller but due to the kernel verification it is better to split go into detail.

    Opaque getResidue.
    Opaque getCarry.
    simpl ; flatten ; try apply withinBounds16 ; try omega.
    simpl ; flatten ; simpl ; try reflexivity.
    simpl ; flatten ; try apply withinBounds16 ; simpl ; try reflexivity.
Qed.*)

Definition Zcar25519 (n:ℤ) : ℤ  :=  38 * getCarry 256 n +  getResidue 256 n.

Notation ℤcar25519 := Zcar25519.

Lemma Zcar25519_correct: forall n, n:𝓖𝓕 = (Zcar25519 n) :𝓖𝓕.
Proof.
  intro n.
  unfold ℤcar25519.
  rewrite  <- Z.add_mod_idemp_l.
  rewrite <- Zmult_mod_idemp_l.
  rewrite <- t2256is38.
  rewrite Zmult_mod_idemp_l.
  rewrite Z.add_mod_idemp_l.
  rewrite Z.add_comm.
  rewrite residuteCarry.
  reflexivity.
  omega.
  compute ; intro ; false.
  compute ; intro ; false.
Qed.

Lemma Carry_n_length_False: forall (h:Z) (q:list Z), Carrying_n 16 15 0 (h :: q) = [] -> False.
Proof. intros ; rewrite Carry_n_step in H ; false. Qed.

Lemma Zshiftr_div_pow2_16: forall a : Z, Z.shiftr a 16 = a / 2 ^ 16.
Proof. intro a ; apply Z.shiftr_div_pow2 ; omega. Qed.


(*
A bunch of facts required to prove getCarry_16_eq_256.
while you could put them all together into a big proof, the kernel verification does not like it.
thus we split it.
*)
Fact factors_256: (2 ^ 256) = (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 *
(2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16)))))))))))))))).
Proof. compute ; reflexivity. Qed.

Fact pre_compute_equality_factor: forall (z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14:Z),
(((((((((((((((z / 2 ^ 16 + z0) / 2 ^ 16 + z1) / 2 ^ 16 + z2) / 2 ^ 16 + z3) / 2 ^ 16 + z4) / 2 ^ 16 + z5) / 2 ^ 16 + z6) / 2 ^ 16 + z7) / 2 ^ 16 + z8) / 2 ^ 16 + z9) / 2 ^ 16 + z10) / 2 ^ 16 + z11) / 2 ^ 16 + z12) / 2 ^ 16 + z13) / 2 ^ 16 + z14) / 2 ^ 16 =
(z + 2 ^ 16 * (z0 + 2 ^ 16 * (z1 + 2 ^ 16 * (z2 + 2 ^ 16 * (z3 + 2 ^ 16 * (z4 + 2 ^ 16 * (z5 + 2 ^ 16 * (z6 + 2 ^ 16 * (z7 + 2 ^ 16 * (z8 + 2 ^ 16 * (z9 + 2 ^ 16 * (z10 + 2 ^ 16 * (z11 + 2 ^ 16 * (z12 + 2 ^ 16 * (z13 + 2 ^ 16 * z14)))))))))))))))
/ 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16 / 2 ^ 16.
Proof.
  intros.
  repeat (rewrite Z.mul_comm ; rewrite Z_div_plus ; [|symmetry; reflexivity] ; rewrite <- Zplus_assoc_reverse).
  rewrite Z.mul_comm ; rewrite Z_div_plus ; [|compute] ; reflexivity.
Qed.

Fact getCarry16_256: forall (z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14:Z),
getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (0 + z) + z0) + z1) + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) + z11) + z12) + z13) + z14) =
getCarry 256 (ℤ16.lst [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]).
Proof.
  intros.
  unfold getCarry in *.
  unfold getResidue in *.
  repeat rewrite Zshiftr_div_pow2_16.
  rewrite Z.shiftr_div_pow2 by omega.
  unfold ZofList.
  rewrite <- Zmult_0_r_reverse.
  rewrite <- Zplus_0_r_reverse.
  change (0 + z) with z.
  rewrite factors_256.
  repeat (rewrite <- Z.div_div ; [|intro ; false | symmetry ; auto]).
  apply pre_compute_equality_factor.
Qed.


Lemma getCarry_16_eq_256 :
forall (z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15:Z) (l:list Z),
Carrying_n 16 15 0 [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14] =  z15 :: l ->
getCarry 16 (nth 15 (z15 :: l) 0) = getCarry 256 (ℤ16.lst [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]).
Proof.
  intros.
  repeat rewrite Carry_n_step in H.
  rewrite Carry_n_step_0 in H.
  repeat (destruct l; tryfalse).
  repeat rewrite ListSame in H.
  jauto_set.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H15.
  unfold nth.
  subst z30.
  apply getCarry16_256.
Qed.

Fact pre_compute_rewrite: forall (z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 : ℤ),
getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 z + z0) + z1) + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) + z11) + z12) + z13) + z14 =
((((((((((((((z / 2 ^ 16 + z0) / 2 ^ 16 + z1) / 2 ^ 16 + z2) / 2 ^ 16 + z3) / 2 ^ 16 + z4) / 2 ^ 16 + z5) / 2 ^ 16 + z6) / 2 ^ 16 + z7) / 2 ^ 16 + z8) / 2 ^ 16 + z9) / 2 ^ 16 + z10) / 2 ^ 16 + z11) / 2 ^ 16 + z12) / 2 ^ 16 + z13) / 2 ^ 16 + z14.
Proof.
  intros.
  unfold getCarry.
  repeat rewrite Zshiftr_div_pow2_16.
  reflexivity.
Qed.

Lemma ℤcar25519_eq_car25519: forall (l : list ℤ), (length l = 16)%nat -> ℤcar25519 (ℤ16.lst l) = ℤ16.lst (car25519 l).
Proof.
  intros l H.
  unfold ℤcar25519.
  unfold car25519.
  apply destruct_length_16 in H.
  do 16 destruct H.
  subst l.
  unfold backCarry.
  flatten ; tryfalse.
  symmetry.
  rewrite Z.add_comm.
  rewrite ZofList_add.
  f_equal.
  (* equality in the carry part *)
  - f_equal.
    apply getCarry_16_eq_256.
    assumption.
  - rewrite Carry_n_step in Eq.
  repeat rewrite ListSame in Eq ; jauto_set.
  subst l z.
  rewrite ZofList_cons.
  rewrite ZofList_app by omega.
  rewrite ZofList_slice by omega.
  rewrite <- CarrynPreserveConst by omega.
  change (0 + x) with x.
  repeat rewrite Carry_n_step ; rewrite Carry_n_step_0.
  remember (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 x + x0) + x1) + x2) + x3) + x4) + x5) + x6) + x7) + x8) + x9) + x10) + x11) + x12) + x13) + x14) as t.
  unfold length.
  unfold nth.
  unfold slice.
  unfold Tools.tail.
  rewrite <- Zred_factor4.
  rewrite Zmult_minus_distr_l.
  rewrite <- Zred_factor4.
  rewrite <- Z.add_sub_assoc.
  rewrite <- Z.add_assoc.
  rewrite <- Zplus_assoc_reverse.
  rewrite residuteCarry by omega.
  rewrite <- Zplus_assoc_reverse.
  rewrite Z.add_sub_assoc.
  rewrite <- ZofList_cons.
  rewrite <- Zmult_assoc_reverse.
  rewrite <- Z.pow_add_r by omega.
  rewrite <- Zmult_assoc_reverse.
  rewrite <- Z.pow_add_r by omega.
  rewrite <- Z.add_opp_r.
  rewrite Zopp_mult_distr_r.
  rewrite <- Z.add_assoc.
  rewrite Zred_factor4.
  rewrite pre_compute_rewrite in Heqt.
  unfold getResidue.
  symmetry.
  rewrite Zmod_eq.
  symmetry.
  rewrite <- Z.add_opp_r.
  f_equal.
  symmetry.
  rewrite Z.mul_comm.
  rewrite Zopp_mult_distr_r.
  change (2 ^ 256) with (2 ^ (16 + 16 * 14) * 2 ^ 16).
  rewrite Zmult_assoc_reverse.
  f_equal.
  rewrite Zmod_eq by (compute ; reflexivity).
  repeat rewrite ZofList_cons_0.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_opp_l.
  rewrite <- Zminus_diag_reverse.
  symmetry ; rewrite Z.sub_0_l.
  rewrite <- Zopp_mult_distr_r.
  f_equal.
  rewrite Z.mul_comm.
  f_equal.
  change (2 ^ (16 + 16 * 14) * 2 ^ 16) with (2^256).
  subst t.
  unfold ZofList.
  rewrite <- Zmult_0_r_reverse.
  rewrite <- Zplus_0_r_reverse.
  rewrite factors_256.
  rewrite pre_compute_equality_factor.
  repeat (rewrite <- Z.div_div; [|compute  ; intro ; false | compute ; reflexivity]).
  reflexivity.
  symmetry.
  reflexivity.
Qed.

Lemma BackCarry_fix: forall l, (length l = 16)%nat -> ℤ16.lst l < 2^256 -> car25519 l = Carrying_n 16 15 0 l.
Proof.
  intros l H Hl.
  unfold car25519.
  unfold backCarry.
  flatten.
  repeat (destruct l ; tryfalse).
  repeat rewrite Carry_n_step in Eq.
  rewrite Carry_n_step_0 in Eq.
  change (0 + z0) with z0.
  repeat (destruct l0; tryfalse).
  repeat rewrite ListSame in Eq ; jauto_set.
  unfold nth.
  unfold slice.
  f_equal.
  - clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H16.
    subst z30.
    rewrite getCarry16_256.
    assert(getCarry 256 (ℤ16.lst [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15]) = 0).
    unfold getCarry.
    rewrite Z.shiftr_div_pow2 by omega.
(*    SearchAbout Z.div 0.*)
    apply Zdiv_small.
  admit.
  admit.
  - change ([z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30]) with
  ([z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29] ++ [z30]).
  f_equal.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H16.
  f_equal.
  rewrite pre_compute_rewrite in H15.
Admitted.
(*
  unfold getResidue.
  subst z30.






Lemma car25519_bound_0 : forall l, (length l = 16)%nat -> nth 0 (car25519 l) 0 < 2 ^ 16.

Lemma car25519_bound_0 : forall l, (length l = 16)%nat -> nth 0 (car25519 l) 0 < 2 ^ 16.
Proof.
  destruct i ; intros l H Hi ; [false|].
  repeat (destruct l ; tryfalse).
  unfold car25519.
  unfold backCarry.
*)