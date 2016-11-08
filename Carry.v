Require Export ZofList.
Require Export Reduce.
Import ListNotations.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma reduce_by_carry_1 :
  forall a b,
    a < 2 ^ n ->
    a + 1 >= 2 ^ n ->
    b = a + 1 - 2 ^ n ->
    b = 0.
Proof.
intros a b Ha1 Ha2 Hb.
omega.
Qed.

Lemma reduce_by_carry_38 :
  forall a b,
    a < 2 ^ 16 ->
    a + 38 >= 2 ^ 16 ->
    b = a + 38 - 2 ^ 16 ->
    b < 2 ^ 16 - 38.
Proof.
intros a b Ha1 Ha2 Hb.
go.
Qed.

Lemma reduce_by_carry_38_256 :
  forall a b,
    a < 2 ^ 256 ->
    a + 38 >= 2 ^ 256 ->
    b = a + 38 - 2 ^ 256 ->
    b < 2 ^ 256 - 38.
Proof.
intros a b Ha1 Ha2 Hb.
go.
Qed.

Lemma reduce_last:
  forall a b,
    a >= 0 ->
    b >= 0 ->
    a < 2 ^ 256 ->
    a + 38 >= 2 ^ 256 ->
    a + 38 - 2 ^ 256 = b ->
    b < 2 ^ 16 - 38.
Proof.
intros a b Ha0 Hb0 Ha1 Ha2 Hb.
go.
Qed.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Definition getCarry (m:Z) : Z :=  Z.shiftr m n.

(* Compute (getCarry (Z.pow 2 18)). *)

Definition getResidute (m:Z) : Z := m mod 2^n.

Lemma getResidute_0 : getResidute 0 = 0.
Proof.
go.
Qed.

Lemma getCarry_0 : getCarry 0 = 0.
Proof.
apply Z.shiftr_0_l.
Qed.

Lemma withinBounds16 : forall m:Z, getResidute m < 2^n.
Proof.
intro m.
unfold getResidute.
apply Z_mod_lt.
apply pown0.
assumption.
Qed.

Lemma residuteCarry : forall m:Z, getResidute m + 2^n *getCarry m = m.
Proof.
intro m.
unfold getResidute.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega.
rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq.
apply pown0.
assumption.
Qed.

Lemma getCarryMonotone : forall m, m > 0 -> getCarry m < m.
Proof.
intros m Hm.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega.
induction m ; go.
- apply Z_div_lt ; go.
assert(2 = 2 ^ 1) by go.
rewrite H at 2; clear H.
rewrite Z.ge_le_iff.
apply Z.pow_le_mono_r_iff ; omega.
- assert (Z.neg p < 0) by apply Zlt_neg_0 ; go.
Qed.


Fixpoint Carrying (a:Z) (l:list Z) : list Z := match a,l with 
| 0,[] => []
| a,[] => [a]
| a,h :: q => getResidute (a + h) :: Carrying (getCarry (a + h)) q
end.

Fixpoint Carrying_n (n:nat) (a:Z) (l:list Z) : list Z := match n,a,l with 
| _,  0,[]     => []
| _,  a,[]     => [a]
| 0%nat,  a,h::q   => (a + h) :: q
| S p,a,h :: q => getResidute (a + h) :: Carrying_n p (getCarry (a + h)) q
end.

Lemma Carry_n_step: forall m a h q, Carrying_n (S m) a (h :: q) = getResidute (a + h) :: Carrying_n m (getCarry (a + h)) q.
Proof.
intros.
simpl.
flatten.
Qed.

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
Proof.
intros.
simpl ; flatten ; reflexivity.
Qed.

Lemma Carrying_n_length: forall l (m:nat) a, (m < length l)%nat -> length (Carrying_n m a l) = length l.
Proof.
induction l as [|h q IHl]; intros [] a Hm; simpl ; flatten ; go.
Qed.


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
reflexivity.
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
replace (ℤ.lst l) with (0 + ℤ.lst l) by go.
apply CarryPreserveConst.
Qed.

Corollary CarrynPreserve : forall m l, ℤ.lst l = ℤ.lst Carrying_n m 0 l.
Proof.
intros.
replace (ℤ.lst l) with (0 + ℤ.lst l) by go.
apply CarrynPreserveConst.
Qed.

End Integer.

Definition backCarry (l:list Z) : (list Z) := 
  match l with
  | [] => []
  | h :: q => let v := nth 15 l 0 in
              (h + 38 * getCarry 16 v) :: slice 14 q ++ [getResidute 16 v]
  end.

Lemma backCarry_ToFF_25519 : forall l, (length l <= 16)%nat -> (ℤ16.lst l) :𝓖𝓕  = ((ℤ16.lst backCarry l) :𝓖𝓕).
Proof.
destruct l as [| h l]; intro Hlength.
- go.
- unfold backCarry.
  rewrite ZofList_cons.
  rewrite ZofList_cons.
  rewrite ZofList_app ; try omega.
  apply le_lt_eq_dec in Hlength.
  destruct Hlength.
  + rename l0 into H.
    replace (nth 15 (h :: l) 0) with 0.
    simpl in H.
    apply lt_S_n in H.
    replace (slice 14 l) with l.
    rewrite getResidute_0.
    rewrite getCarry_0.
    replace (ℤ16.lst [0]) with 0.
    f_equal.
    ring.
    go.
    symmetry.
    apply slice_length_le.
    omega.
    symmetry.
    apply nth_overflow.
    omega.
  + rename e into H.
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    {
      clear H.
      replace (nth 15 [h; z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13] 0) with z13 by go.
      replace (slice 14 [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with 
      [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] by go.
      replace ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] ++ [ z13]) by go.
      rewrite ZofList_app ; try omega.
      replace (length [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12]) with 14%nat by go.
      replace (ℤ16.lst [getResidute 16 z13]) with (getResidute 16 z13) by go.
      replace (ℤ16.lst [z13]) with z13 by go.
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
      replace 256 with (16 + 16 * 15) by omega.
      rewrite Z.pow_add_r by omega.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_mod.
      f_equal.
      f_equal.
      replace (2 ^ (16 * 15)) with (2 ^ (16 * 14) * 2 ^ 16) by (compute ; omega).
      replace (ℤ.ℕ 14) with 14 by (compute ; omega).
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod.
      f_equal.
      f_equal.
      rewrite Z.add_comm.
      rewrite residuteCarry ; go.
    }
    inversion H.
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
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [|false].
unfold car25519.
unfold backCarry.
flatten. symmetry ; reflexivity.
change
    (nth (S i) (z15 + 38 * getCarry 16 (nth 15 (z15 :: l) 0)
      :: slice 14 l ++ [getResidute 16 (nth 15 (z15 :: l) 0)]) 0)
  with 
   (nth i (slice 14 l ++ [getResidute 16 (nth 15 (z15 :: l) 0)]) 0).
rewrite! Carry_n_step in Eq.
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
rewrite! ListSame in Eq.
jauto_set.
clear Hi.
(* destruct the big /\ construction *)
assert(Hi: (i < 14 \/ i = 14 \/ i > 14)%nat) by omega.
(* case analisys on i: in slice, last elem or outside *)
case Hi ; intro Hi_temp ; clear Hi ; rename Hi_temp into Hi.
(* IN *)
{
  rewrite app_nth1.
  - replace (slice 14
      (z16:: z17 :: z18 :: z19 :: z20 :: z21 :: z22 :: z23 :: z24 :: z25 :: z26 :: z27 :: z28 :: z29 :: Carrying_n 16 0 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (0 + z) + z0) + z1) + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) + z11) + z12) + z13)) [z14])) with 
      (z16 :: z17 :: z18 :: z19 :: z20 :: z21 :: z22 :: z23 :: z24 :: z25 :: z26 :: z27 :: z28 :: z29 :: []).
    + simpl ; flatten ; subst ; try (apply withinBounds16 ; omega) ; simpl ; flatten ; symmetry ; reflexivity.
    + rewrite! slice_cons' ; rewrite slice_nil ; reflexivity.
  - rewrite slice_length_min ; auto.
}
case Hi ; intro Hi_temp ; clear Hi ; rename Hi_temp into Hi.
{
  subst i.
  replace (slice 14
     (z16:: z17 :: z18 :: z19 :: z20 :: z21 :: z22 :: z23 :: z24 :: z25 :: z26 :: z27 :: z28 :: z29 :: l)) with 
     (z16 :: z17 :: z18 :: z19 :: z20 :: z21 :: z22 :: z23 :: z24 :: z25 :: z26 :: z27 :: z28 :: z29 :: []).
  (* main goal *)
  - rewrite app_nth2.
  change (length [z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29]) with 14%nat.
  rewrite NPeano.Nat.sub_diag.
  unfold nth.
  apply withinBounds16 ; omega.
  (* goals generated by change *)
  compute ; omega.
  (* goals generated by replace *)
  - rewrite! slice_cons' ; rewrite slice_nil ; reflexivity.
}
{ rewrite nth_overflow.
  symmetry ; reflexivity.
  rewrite app_length.
  rewrite slice_length_min.
  compute.
  omega.
}
Qed.

(*
    Proof could be smaller but due to the kernel verification it is better to split go into detail.

    Opaque getResidute.
    Opaque getCarry.
    simpl ; flatten ; try apply withinBounds16 ; try omega.
    simpl ; flatten ; simpl ; try reflexivity.
    simpl ; flatten ; try apply withinBounds16 ; simpl ; try reflexivity.
Qed.*)


Definition ℤcar25519 (n:ℤ) : ℤ  :=  38 * getCarry 256 n +  getResidute 256 n.

Lemma ℤcar25519_correct: forall n, n:𝓖𝓕 = (ℤcar25519 n) :𝓖𝓕.
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
Proof.
intros.
rewrite Carry_n_step in H.
false.
Qed.

Lemma Zshiftr_div_pow2_16: forall a : ℤ,Z.shiftr a 16 = a / 2 ^ 16.
Proof.
intro a.
apply Z.shiftr_div_pow2.
omega.
Qed.

Lemma ℤcar25519_eq_car25519: forall (l : list ℤ), (length l = 16)%nat -> ℤcar25519 (ℤ16.lst l) = ℤ16.lst (car25519 l).
Proof.
intros l Hlength.
unfold ℤcar25519.
unfold car25519.
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [false|].
destruct l ; [|false].
unfold backCarry.
flatten.
false.
symmetry.
rewrite Z.add_comm.
rewrite ZofList_add.
f_equal.
(* equality in the carry part *)
  {
  rewrite! Carry_n_step in Eq.
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; [false|].
  destruct l ; rewrite! ListSame in Eq ; jauto_set.
  apply list_to_length in H14 ;rewrite Carrying_n_length in H14 ; [| compute ; auto] ; false.
  assert(Hz30:= H14).
  apply list_to_length in H14 ; rewrite Carrying_n_length in H14 ; [| compute ; auto].
  simpl in H14 ; inversion H14 ; symmetry in H16 ; rewrite <- lengthNil in H16 ; subst l ; clear H14.
  replace (nth 15 [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30] 0) with z30 by auto.
  replace (slice 14 [z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30]) with [z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29] by (compute ; auto).
  unfold getCarry in *.
  unfold getResidute in *.
  rewrite! Zshiftr_div_pow2_16 in *.
  rewrite! Z.shiftr_div_pow2 in * by omega.
  replace (z15 + 38 * (z30 / 2 ^ 16)) with (38 * (z30 / 2 ^ 16) + z15) by ring.
  replace ([z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29] ++ [z30 mod 2 ^ 16])
  with ([z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29 ; z30 mod 2 ^ 16]) by reflexivity.
  rewrite Carry_n_step_0 in Hz30 ; apply headSame in Hz30.
  f_equal.
  subst z30.
  clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 Hlength.
  rewrite! ZofList_cons.
  rewrite ZofList_nil.
  rewrite <- Zmult_0_r_reverse.
  rewrite <- Zplus_0_r_reverse.
  change (0 + z) with z.
  change (2 ^ 256) with (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 *
  (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16)))))))))))))))).
  repeat (rewrite <- Z.div_div; [|compute  ; intro ; false | compute ; reflexivity]).
  repeat (rewrite Z.mul_comm ; rewrite Z_div_plus ; [|compute ; reflexivity] ; rewrite <- Zplus_assoc_reverse).
  rewrite Z.mul_comm ; rewrite Z_div_plus ; [|compute] ;
  reflexivity.
}
rewrite Carry_n_step in Eq.
rewrite! ListSame in Eq ; jauto_set.
subst l z15.
rewrite ZofList_cons.
rewrite ZofList_app by omega.
rewrite ZofList_slice by omega.
rewrite <- CarrynPreserveConst by omega.
replace ((ℤ.ℕ length (slice 14 (Carrying_n 16 14 (getCarry 16 (0 + z)) [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14])))) with 14
  by (repeat rewrite Carry_n_step ; rewrite Carry_n_step_0 ; simpl ; reflexivity).
change (0 + z) with z.
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
repeat rewrite Carry_n_step.
rewrite Carry_n_step_0.
repeat rewrite nth_cons.
rewrite nth_cons_0.
repeat rewrite tail_cons.
rewrite tail_cons_0.
assert(Htemp: exists t, t = getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 z + z0) + z1) + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) + z11) + z12) + z13) + z14).
exists (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 z + z0) + z1) + z2) + z3) + z4) + z5) + z6) + z7) + z8) + z9) + z10) + z11) + z12) + z13) + z14) ; reflexivity.
destruct Htemp as [t Htemp].
rewrite <- Htemp.
rewrite <- Z.add_opp_r.
rewrite Zopp_mult_distr_r.
rewrite <- Z.add_assoc.
rewrite Zred_factor4.
unfold getCarry in Htemp.
repeat rewrite Zshiftr_div_pow2_16 in Htemp.
unfold getResidute.
symmetry.
rewrite Zmod_eq by (compute ; reflexivity).
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
subst t.
repeat rewrite ZofList_cons.
rewrite ZofList_nil.
rewrite <- Zmult_0_r_reverse.
rewrite <- Zplus_0_r_reverse.
change (2 ^ (16 + 16 * 14) * 2 ^ 16) with (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 *
 (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16)))))))))))))))).
  repeat (rewrite <- Z.div_div; [|compute  ; intro ; false | compute ; reflexivity]).
  repeat (rewrite Z.mul_comm ; rewrite Z_div_plus ; [|compute ; reflexivity] ; rewrite <- Zplus_assoc_reverse).
  rewrite Z.mul_comm ; rewrite Z_div_plus ; [|compute] ;
  reflexivity.
Qed.

(* Yes I'm kinda cheating by fixing the length to 16 ! but it is still correct if
you were to compare to the tweetnacl implementation*)

