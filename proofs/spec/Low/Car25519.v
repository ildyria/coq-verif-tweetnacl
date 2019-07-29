Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Low.Carry_n.
From Tweetnacl Require Import Low.BackCarry.
From Tweetnacl Require Import Low.Carry.

Local Open Scope Z.

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

Lemma car25519_bound_sup : forall i l, (length l = 16)%nat -> (i <> 0)%nat -> 0 <= nth i (car25519 l) 0 < 2 ^ 16.
Proof.
  intros i l H Hi.
  apply destruct_length_16 in H.
  do 16 destruct H.
  unfold car25519.
  subst.
  repeat match goal with
    | _ => rewrite Carry_n_step
    | _ => rewrite Carry_n_step_0
  end ; simpl ; flatten;
  repeat match goal with
    | _ => eapply getResidue_bounds
    | _ => omega
    | _ => compute; split ; [intro|] ; go
  end.
Qed.

Lemma car25519_bound_Z : forall (i:nat) l, Zlength l = 16 -> 0 <> i -> nth i (car25519 l) 0 < 2 ^ 16.
Proof. convert_length_to_Zlength car25519_bound_sup. Qed.

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
  orewrite Z.shiftr_div_pow2.
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
  orewrite Z.shiftr_div_pow2.
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
  move: H ; rewrite ?ListSame => H.
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
  - move: Eq ; rewrite Carry_n_step2 ?ListSame => Eq ; jauto_set.
  subst l z.
  rewrite ZofList_cons.
  orewrite ZofList_app.
  orewrite ZofList_take.
  rewrite <- CarrynPreserveConst ; try omega.
  change (0 + x) with x.
  repeat rewrite Carry_n_step2 ; rewrite Carry_n_step_02.
  remember (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 (getCarry 16 x + x0) + x1) + x2) + x3) + x4) + x5) + x6) + x7) + x8) + x9) + x10) + x11) + x12) + x13) + x14) as t.
  unfold length, nth, take, drop.
  rewrite -Zred_factor4 Zmult_minus_distr_l -Zred_factor4 -Z.add_sub_assoc -Z.add_assoc.
  rewrite -Zplus_assoc_reverse;
  orewrite residuteCarry.
  rewrite -Zplus_assoc_reverse Z.add_sub_assoc -ZofList_cons -Zmult_assoc_reverse -Z.pow_add_r.
  2: (compute ; go).
  rewrite <- Zmult_assoc_reverse.
  rewrite <- Z.pow_add_r by (compute ; go).
  rewrite -Z.add_opp_r Zopp_mult_distr_r -Z.add_assoc -Zred_factor4.
  simpl Z.succ.
  rewrite pre_compute_rewrite in Heqt.
  repeat orewrite getResidue_mod_eq.
  unfold getResidue_mod.
  symmetry.
  orewrite Zmod_eq.
  2: (compute ; reflexivity).
  symmetry.
  rewrite <- Z.add_opp_r.
  f_equal.
  symmetry.
  rewrite Z.mul_comm Zopp_mult_distr_r.
  change (2 ^ 256) with (2 ^ (16 + 16 * 14) * 2 ^ 16).
  rewrite Zmult_assoc_reverse.
  orewrite Zmod_eq.
  2: compute ; reflexivity.
  rewrite ?ZofList_cons_0.
  symmetry.
  change (16 * 13 + 16 * 1) with (16 * 14).
  2: compute ; intro ; false.
  rewrite Zred_factor4.
  f_equal.
  rewrite <- Zopp_mult_distr_r.
  rewrite Z.add_sub_assoc.
  rewrite Z.add_opp_l.
  rewrite Z.sub_diag.
  rewrite Z.sub_0_l.
  f_equal.
  rewrite Z.mul_comm.
  f_equal.
  subst t.
  unfold ZofList.
  rewrite <- Zmult_0_r_reverse.
  rewrite <- Zplus_0_r_reverse.
  change (2 ^ (16 + 16 * 14) * 2 ^ 16) with (2^256).
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
  move : Eq ; rewrite ?Carry_n_step2 Carry_n_step_02.
  change (0 + z0) with z0 => Eq.
  repeat (destruct l0; tryfalse).
  move: Eq ; rewrite ?ListSame => Eq ; jauto_set ; try reflexivity.
(*   clear H H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18. *)
  unfold nth.
  - subst z30.
    rewrite getCarry16_256.
    assert(getCarry 256 (ℤ16.lst [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15]) = 0).
    apply getCarry_impl_0 ; omega.
    omega.
  - unfold getResidue.
  erewrite (getCarry_16_eq_256 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15).
  2: rewrite ?Carry_n_step2 Carry_n_step_02 ; change (0 + z0) with z0; rewrite ?ListSame ; jauto_set ; try assumption.
    assert(getCarry 256 (ℤ16.lst [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15]) = 0).
    apply getCarry_impl_0 ; omega.
  clear H19 H18 H17 H16 H15 H14 H13 H13 H12 H11 H10 H9 H8 H7 H6 H5 H4 H3 H2 H.
    simpl nth.
    assert(getCarry 256 (ℤ16.lst [z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14; z15]) = 0).
    apply getCarry_impl_0 ; omega.
  rewrite H.
  change (0 ≪ 16) with 0. omega.
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


Lemma car25519_length : forall l,
  length l = 16%nat ->
  length (car25519 l) = 16%nat.
Proof.
  intros.
  apply destruct_length_16 in H.
  do 16 destruct H.
  subst.
  unfold car25519.
  repeat rewrite Carry_n.Carry_n_step.
  rewrite Carry_n.Carry_n_step_0.
  reflexivity.
Qed.

Lemma car25519_Zlength : forall l,
  Zlength l = 16 -> 
  Zlength (car25519 l) = 16.
Proof. convert_length_to_Zlength car25519_length. Qed.

Close Scope Z.