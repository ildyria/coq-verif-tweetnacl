Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Car.Reduce.
Require Import Tweetnacl.Car.Carry_n.
Require Import Tweetnacl.Op.M.

Require Import stdpp.prelude.


Local Open Scope Z.
Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.


Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Fixpoint Carrying (a:Z) (l:list Z) : list Z := match a,l with 
| 0,[] => []
| a,[] => [a]
| a,h :: q => getResidue n (a + h) :: Carrying (getCarry n (a + h)) q
end.

Lemma Carrying_n_eq: forall l (m:nat) a, m = length l -> Carrying_n n m a l = Carrying a l.
Proof.
  induction l as [|h q IHl]; intros m a Hm; go.
  destruct m.
  inv Hm.
  simpl in *.
  inversion Hm.
  replace (h + a) with (a + h) by omega.
  flatten ; f_equal ; go.
Qed.

Lemma Carrying_n_eq_Z: forall l (m:nat) a, Zlength l = m -> Carrying_n n m a l = Carrying a l.
Proof. convert_length_to_Zlength Carrying_n_eq. Qed.

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

Corollary CarryPreserve : forall l, ℤ.lst l = ℤ.lst Carrying 0 l.
Proof.
  intros.
  symmetry.
  rewrite Zplus_0_r_reverse.
  symmetry.
  rewrite Z.add_comm.
  apply CarryPreserveConst.
Qed.

End Integer.

Definition backCarry (l:list Z) : (list Z) := 
  match l with
  | [] => []
  | h :: q => let v := nth 15 l 0 in
              (h + 38 * getCarry 16 v) :: take 14 q ++ [getResidue 16 v]
  end.

Lemma backCarry_ToFF_25519 : forall l, Zlength l <= 16 -> (ℤ16.lst l) :𝓖𝓕  = ((ℤ16.lst backCarry l) :𝓖𝓕).
Proof.
  destruct l as [| h l]; intro Hlength.
  - go.
  - unfold backCarry.
    repeat rewrite ZofList_cons.
    rewrite ZofList_app ; try omega.
    rewrite Zlength_cons' in Hlength.
    apply Z_le_lt_eq_dec in Hlength.
    destruct Hlength.
    + rename l0 into H.
      assert(Zlength l < 15) by omega.
      rewrite nth_overflow.
      rewrite take_ge.
      rewrite getResidue_0.
      rewrite getCarry_0.
      rewrite ZofList_cons_0.
      f_equal.
      ring.
      omega.
      rewrite Zlength_correct in H0; omega.
      rewrite Zlength_correct in H0 ; simpl ; omega.
    + rename e into H.
      assert((length l = 15)%nat).
      rewrite Zlength_correct in H ; omega.
      repeat (destruct l ; tryfalse).
      clear H H0.
      unfold nth.
      unfold take.
      change ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] ++ [ z13]).
      rewrite ZofList_app ; try omega.
      simpl Zlength.
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

Lemma car25519_ToFF_25519 : forall l, Zlength l = 16 -> (ℤ16.lst l) :𝓖𝓕  = (ℤ16.lst car25519 l) :𝓖𝓕.
Proof.
  intros l Hlength.
  unfold car25519.
  erewrite <- backCarry_ToFF_25519.
  rewrite <- CarrynPreserve ; try omega.
  rewrite Carrying_n_Zlength ; go.
  rewrite Zlength_correct in Hlength ; simpl ; omega.
Qed.

Lemma car25519_bound_sup : forall i l, (length l = 16)%nat -> (i <> 0)%nat -> nth i (car25519 l) 0 < 2 ^ 16.
Proof.
  destruct i ; intros l H Hi ; [false|].
  apply destruct_length_16 in H.
  do 16 destruct H.
  unfold car25519.
  unfold backCarry.
  flatten. symmetry ; reflexivity.
  rewrite nth_lookup.
  unfold lookup. unfold list_lookup.
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
    unfold take.
    simpl ; unfold lookup ; flatten; simpl ; subst ; try (apply getResidue_bounds ; omega).
    reflexivity.
  }
  case Hi ; intro Hi_temp ; clear Hi ; rename Hi_temp into Hi.
  {
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13.
    subst i.
    simpl.
    apply getResidue_bounds ; omega.
  }
  {
    clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
    simpl.
    replace ([z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; getResidue 16 z14] !! i) with (None:option Z).
    reflexivity.
    symmetry.
    rewrite lookup_ge_None.
    simpl ; omega.
  }
Qed.


Lemma car25519_bound_Z : forall (i:nat) l, Zlength l = 16 -> 0 <> i -> nth i (car25519 l) 0 < 2 ^ 16.
Proof. convert_length_to_Zlength car25519_bound_sup. Qed.

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

(*
A bunch of facts required to prove getCarry_16_eq_256.
while you could put them all together into a big proof, the kernel verification does not like it.
thus we split it.
*)

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

Fact factors_240
     : 2 ^ 240 =
       (2 ^ 16 *
        (2 ^ 16 *
         (2 ^ 16 *
          (2 ^ 16 *
           (2 ^ 16 *
            (2 ^ 16 *
             (2 ^ 16 *
              (2 ^ 16 *
               (2 ^ 16 *
                (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * 2 ^ 16)))))))))))))).
Proof. compute ; reflexivity. Qed.

Fact getCarry16_240: forall (z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14:Z),
getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (0 + z) + z0) + z1) + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) + z11) + z12) + z13) + z14 =
getCarry 240 (ℤ16.lst [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]).
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
  rewrite factors_240.
  repeat (rewrite <- Z.div_div ; [|intro ; false | symmetry ; auto]).
  repeat (rewrite Z.mul_comm ; rewrite Z_div_plus ; [|symmetry; reflexivity] ; rewrite <- Zplus_assoc_reverse).
  rewrite Z.mul_comm ; rewrite Z_div_plus ; [|compute] ; reflexivity.
Qed.

Lemma getCarry_16_eq_256 :
forall (z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15:Z) (l:list Z),
Carrying_n 16 15 0 [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14] =  z15 :: l ->
getCarry 16 (nth 15 (z15 :: l) 0) = getCarry 256 (ℤ16.lst [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]).
Proof.
  intros.
  repeat rewrite Carry_n_step2 in H.
  rewrite Carry_n_step_02 in H.
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

Lemma ℤcar25519_eq_car25519_length: forall (l : list ℤ), (length l = 16)%nat -> ℤcar25519 (ℤ16.lst l) = ℤ16.lst (car25519 l).
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
  - rewrite Carry_n_step2 in Eq.
  repeat rewrite ListSame in Eq ; jauto_set.
  subst l z.
  rewrite ZofList_cons.
  rewrite ZofList_app by omega.
  rewrite ZofList_take by omega.
  rewrite <- CarrynPreserveConst by omega.
  change (0 + x) with x.
  repeat rewrite Carry_n_step2 ; rewrite Carry_n_step_02.
  remember (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 x + x0) + x1) + x2) + x3) + x4) + x5) + x6) + x7) + x8) + x9) + x10) + x11) + x12) + x13) + x14) as t.
  unfold length.
  unfold nth.
  unfold take.
  unfold drop.
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
  rewrite <- Z.pow_add_r by (compute ; go).
  rewrite <- Zmult_assoc_reverse.
  rewrite <- Z.pow_add_r by (compute ; go).
  rewrite <- Z.add_opp_r.
  rewrite Zopp_mult_distr_r.
  rewrite <- Z.add_assoc.
  rewrite Zred_factor4.
  rewrite pre_compute_rewrite in Heqt.
  repeat rewrite getResidue_mod_eq by omega.
  unfold getResidue_mod.
  symmetry.
  rewrite Zmod_eq by reflexivity.
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
Qed.

Lemma ℤcar25519_eq_car25519_Zlength: forall (l : list ℤ), Zlength l = 16 -> ℤcar25519 (ℤ16.lst l) = ℤ16.lst (car25519 l).
Proof. convert_length_to_Zlength ℤcar25519_eq_car25519_length. Qed.

Lemma BackCarry_fix_length: forall l, (length l = 16)%nat -> 0 <= ℤ16.lst l < 2^256 -> car25519 l = Carrying_n 16 15 0 l.
Proof.
  intros l H Hl.
  unfold car25519.
  unfold backCarry.
  flatten.
  repeat (destruct l ; tryfalse).
  repeat rewrite Carry_n_step2 in Eq.
  rewrite Carry_n_step_02 in Eq.
  change (0 + z0) with z0.
  repeat (destruct l0; tryfalse).
  repeat rewrite ListSame in Eq ; jauto_set.
  clear H H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18.
  unfold nth.
  unfold take.
  f_equal.
  - subst z30.
    rewrite getCarry16_256.
    assert(getCarry 256 (ℤ16.lst [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15]) = 0).
    apply getCarry_impl_0 ; omega.
    omega.
  - change ([z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30]) with
  ([z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29] ++ [z30]).
  f_equal ; f_equal.
  unfold getResidue.
    subst z30.
    repeat rewrite getCarry16_256.
    assert(getCarry 256 (ℤ16.lst [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15]) = 0).
    apply getCarry_impl_0 ; omega.
  rewrite H.
  simpl Z.shiftl.
  rewrite <- Zminus_0_l_reverse.
  reflexivity.
Qed.

Lemma BackCarry_fix_Zlength: forall l, Zlength l = 16 -> 0 <= ℤ16.lst l < 2^256 -> car25519 l = Carrying_n 16 15 0 l.
Proof. convert_length_to_Zlength BackCarry_fix_length. Qed.

Lemma bounds_car_sup_length: forall i l, (length l = 16)%nat -> 0 <= ℤ16.lst l < 2^256 -> 
  nth i (car25519 l) 0 < 2 ^ 16.
Proof.
  intros i.
  assert(Hi: i <> 0%nat \/ i = 0%nat) by omega.
  destruct Hi.
  intros ; apply car25519_bound_sup ; auto.
  intros l Hl Hlb.
  rewrite BackCarry_fix_length ; auto.
  subst i.
  destruct l ; [false|].
  simpl.
  apply getResidue_bounds.
  omega.
Qed.

Lemma bounds_car_sup_Zlength: forall i l, Zlength l = 16 -> 0 <= ℤ16.lst l < 2^256 -> 
  nth i (car25519 l) 0 < 2 ^ 16.
Proof. convert_length_to_Zlength bounds_car_sup_length. Qed.

Lemma bounds_car_inf_length: forall i l, (length l = 16)%nat -> 0 <= ℤ16.lst l < 2^256 -> 0 <= nth i (car25519 l) 0.
Proof.
  intros ; rewrite BackCarry_fix_length ; auto.
  flatten ; repeat (destruct l ; tryfalse).
  repeat rewrite Carry_n_step2.
  rewrite Carry_n_step_02.
  unfold nth.
  flatten ; try apply getResidue_bounds; try omega.
  rewrite getCarry16_240.
  apply getCarry_pos.
  omega.
  omega.
Qed.

Lemma bounds_car_inf_Zlength: forall i l, Zlength l = 16 -> 0 <= ℤ16.lst l < 2^256 -> 0 <= nth i (car25519 l) 0.
Proof. convert_length_to_Zlength bounds_car_inf_length. Qed.