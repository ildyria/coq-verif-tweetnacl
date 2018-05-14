Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.Carry.
From Tweetnacl Require Import Mid.ZCarry.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Low.Car25519.

Open Scope Z.

(*Eval simpl in (ZofList_Bound 16 16 (2 ^ 62) < 1 * 2^303).*)

Theorem Zcar25519_bounds_length:
  forall l1 l2 l3,
    length l1 = 16%nat ->
    length l2 = 16%nat -> (* not required but easier *)
    length l3 = 16%nat -> (* not required but easier *)
    Forall (fun x => -2^62 < x < 2^62) l1 ->
    l2 = car25519 l1 ->
    l3 = car25519 l2 ->
    Forall (fun x => 0 <= x < 2^16) (car25519 l3).
Proof.
  intros l1 l2 l3 Hl1 Hl2 Hl3 HForalll1 Hcarr1 Hcarr2.
  apply Forall_lookup.
  intros i x Hl.
  apply (nth_lookup_Some _ _ 0) in Hl ; subst x.
  assert(Hbounds:= Hl1).
  apply (ZofList_bounds 16 l1 16 (-2^62) (2^62)) in Hbounds ; auto.
  split; [apply bounds_car_inf_length| apply bounds_car_sup_length] ; auto;
  try assumption ; rewrite Hcarr2;
  rewrite <- ℤcar25519_eq_car25519_length by assumption;
  eapply (doubleCar_ext_str (ℤ16.lst l1) _ 303) ;
  try omega ; 
  try (eapply bounds.le_lt_trans ; [eapply Hbounds | | ] ; compute ; reflexivity);
  try (rewrite ℤcar25519_eq_car25519_length ; auto ; try rewrite Hcarr1 ; reflexivity).
Qed.

Theorem Zcar25519_bounds_Zlength:
  forall l1 l2 l3,
    Zlength l1 = 16 ->
    Zlength l2 = 16 -> (* not required but easier *)
    Zlength l3 = 16 -> (* not required but easier *)
    Forall (fun x => -2^62 < x < 2^62) l1 ->
    l2 = car25519 l1 ->
    l3 = car25519 l2 ->
    Forall (fun x => 0 <= x < 2^16) (car25519 l3).
Proof.
  intros l1 l2 l3 Hl1 Hl2 Hl3 HForalll1 Hcarr1 Hcarr2.
  apply Forall_lookup.
  intros i x Hl.
  apply (nth_lookup_Some _ _ 0) in Hl ; subst x.
  assert(Hbounds:= Hl1).
  apply (ZofList_bounds_Zlength 16 l1 16 (-2^62) (2^62)) in Hbounds ; auto.
  split; [apply bounds_car_inf_Zlength| apply bounds_car_sup_Zlength] ; auto;
  try assumption ; rewrite Hcarr2;
  rewrite <- ℤcar25519_eq_car25519_Zlength by assumption;
  eapply (doubleCar_ext_str (ℤ16.lst l1) _ 303) ;
  try omega ;
  try (eapply bounds.le_lt_trans ; [eapply Hbounds | | ] ; compute ; reflexivity);
  try (rewrite ℤcar25519_eq_car25519_Zlength ; auto ; try rewrite Hcarr1 ; reflexivity).
Qed.

Ltac assert_base_lemmas:=
  assert(H216262: 2^16 < 2^63) by reflexivity;
  assert(H216247: 2^16 < 2^16 + 38 *2^47) by reflexivity;
  assert(H247262: 2^16 + 38 *2^47 < 2^63) by reflexivity;
  assert(H262263: 2^62 < 2^63) by reflexivity;
  assert(H263262: - 2^63 < - 2^62) by reflexivity;
  assert(H2630: - 2^63 < 0) by reflexivity;
  assert(H2460: 38 * - 2^47 < 0) by reflexivity;
  assert(H263246: - 2^63 < 38 * - 2^47) by reflexivity;
  assert(H160 : 16 > 0) by reflexivity;
  assert(HH : forall k, 0 ≤ getResidue 16 k ∧ getResidue 16 k < 2 ^ 16) by (clear ; intro; eapply getResidue_bounds ; omega).


Theorem Zcar25519_bounds_length_1:
  forall l1,
    length l1 = 16%nat ->
    Forall (fun x => -2^62 < x < 2^62) l1 ->
    Forall (fun x => 38 * -2^47 <= x < 2^16 + 38 *2^47) (car25519 l1).
Proof.
  intros l1 H HForalll1.
  apply Forall_lookup.
  intros i x Hl.
  apply (nth_lookup_Some _ _ 0) in Hl ; subst x.
  apply destruct_length_16 in H.
  do 16 destruct H.
  subst.
  move: HForalll1 ; rewrite ?Forall_cons => HForalll1.
  repeat match goal with
    | [H : (_ /\ _) /\ _ |-_] => destruct H
  end.
  clear H15.
  assert_base_lemmas.
  unfold car25519.
  repeat match goal with
    | _ => rewrite Carry_n.Carry_n_step
    | _ => rewrite Carry_n.Carry_n_step_0
  end ; simpl ; flatten ;  
  repeat match goal with
    | _ => omega
    | [ HH : context[getResidue] |- _ ∧ getResidue 16 (?x) < _ ] => specialize HH with x
    | [ |- 38 * - 2 ^ 47 <= 0 ∧ 0 < 2^16 + 38 * 2 ^ 47 ] => compute ; split; [intro ; tryfalse | reflexivity]
    | _ => apply Add_interval_mono3
    | _ => apply Mult_interval_correct_pos_le
    | [ |- -2^47 <= getCarry _ _ ∧ _ <= _ ] => apply getCarry_bound_str47
    | [ |- context[2 ^ 63] ] => change (-2^63) with ((-2^62) + (-2^62)); change (2^63) with ((2^62) + (2^62))
    | [ |- _ < _ ∧ _ < _ ] => apply Add_interval_mono
    | [ |- -2^62 < getCarry _ _ ∧ _ < _ ] => apply getCarry_bound_str63
  end.
Qed.

Lemma Zcar25519_exact_bounds_0:
  forall l,
    length l = 16%nat -> 
     Forall (fun x => -2^62 < x < 2^62) l ->
    38 * -2^47 <= nth 0 (car25519 l) 0  < 2^16 + 38 *2^47.
Proof.
  intros l H HForalll1.
  apply destruct_length_16 in H.
  do 16 destruct H.
  subst.
  assert_base_lemmas.
  move: HForalll1 ; rewrite ?Forall_cons => HForalll1.
  repeat match goal with
    | [H : (_ /\ _) /\ _ |-_] => destruct H
    | _ => progress unfold car25519
    | _ => rewrite Carry_n.Carry_n_step
    | _ => rewrite Carry_n.Carry_n_step_0; simpl
    | _ => omega
    | [ HH : context[getResidue] |- _ ∧ getResidue 16 (?x) < _ ] => specialize HH with x
    | [ |- 38 * - 2 ^ 47 <= 0 ∧ 0 < 2^16 + 38 * 2 ^ 47 ] => compute ; split; [intro ; tryfalse | reflexivity]
    | _ => apply Add_interval_mono3
    | _ => apply Mult_interval_correct_pos_le
    | [ |- -2^47 <= getCarry _ _ ∧ _ <= _ ] => apply getCarry_bound_str47
    | [ |- context[2 ^ 63] ] => change (-2^63) with ((-2^62) + (-2^62)); change (2^63) with ((2^62) + (2^62))
    | [ |- _ < _ ∧ _ < _ ] => apply Add_interval_mono
    | [ |- -2^62 < getCarry _ _ ∧ _ < _ ] => apply getCarry_bound_str63
  end.
Qed.

Theorem Zcar25519_bounds_length_2:
  forall l1 l2,
    length l1 = 16%nat ->
    length l2 = 16%nat ->
    Forall (fun x => -2^62 < x < 2^62) l1 ->
    l2 = car25519 l1 ->
    Forall (fun x => -38 <= x < 2^16 + 38) (car25519 l2).
Proof.
  intros l1 l2 Hl1 Hl2 HForalll1 Hcarr1.
  apply Forall_lookup.
  intros i x Hl.
  apply (nth_lookup_Some _ _ 0) in Hl ; subst x.
  assert(Hbounds:= Hl1).
  apply (ZofList_bounds 16 l1 16 (-2^62) (2^62)) in Hbounds ; auto.
  assert(38 * -2^47 <= ℤ16.lst (car25519 l1) < 2^257).
  rewrite <- ℤcar25519_eq_car25519_length by omega.
  remember( ℤ16.lst l1) as x.
  assert(x < 0 \/ 0 <= x) by omega.
  assert(256 ≤ 303 ∧ 303 < 512) by (compute ; split ; [intro ; tryfalse | reflexivity]).
  destruct H.
  - assert( - 2 ^ 303 < x).
    change (ZofList_Bound 16 16 (- 2 ^ 62)) with  (-8148268238044213330262537980352300734732221417397775119962774120020674928590150695349387264) in Hbounds.
    change (-2^303) with (-16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008).
    omega.
    apply (ZCarry25519_neg_str x 303 H0) in H1.
    2: omega.
    simpl in H1.
    assert(2^256 < 2^257) by (compute ; reflexivity).
    omega.
  - split.
    assert(0 ≤ ℤcar25519 x).
    apply ZCarry25519_pos.
    assumption.
    assert(38 * - 2 ^ 47 < 0) by (compute ; reflexivity).
    omega.
    assert( x < 2 ^ 303).
      change (ZofList_Bound 16 16 (2 ^ 62)) with  (8148268238044213330262537980352300734732221417397775119962774120020674928590150695349387264) in Hbounds.
      change (2^303) with (16296287810675888690147565507275025288411747149327490005089123594835050398106693649467179008).
      omega.
    apply (ZCarry25519_sup_bounds_str3 x 303) in H0.
    2: omega.
    assert(2 ^ 256 - 38 + 2 ^ 256 < 2^257) by ( compute; reflexivity).
    omega.
  - assert(Hi: i <> 0%nat \/ i = 0%nat ) by omega.
    destruct Hi.
    assert( 0 <= nth i (car25519 l2) 0 < 2 ^ 16).
    apply car25519_bound_sup ; go.
    assert(2^16 < 2^17) by (compute; reflexivity).
    omega.
    subst i.

    rewrite <- Hcarr1 in H.
    unfold car25519.
    unfold BackCarry.backCarry.
    rename H into Hbound_strict.
    rename Hl2 into H.
    apply destruct_length_16 in H.
    do 16 destruct H.
    subst.
  assert(HH : forall k, 0 ≤ getResidue 16 k ∧ getResidue 16 k < 2 ^ 16) by (clear ; intro; eapply getResidue_bounds ; omega).
  assert(H216217: 2^16 < 2^17) by reflexivity.
  assert(H0217: 0 < 2^17) by reflexivity.
  repeat match goal with
    | _ => rewrite Carry_n.Carry_n_step
    | _ => rewrite Carry_n.Carry_n_step_0
  end.
  erewrite getCarry_16_eq_256.
  
  2: {
    repeat match goal with
    | _ => rewrite Carry_n.Carry_n_step
    | _ => rewrite Carry_n.Carry_n_step_0
  end.
  f_equal.
  }

  unfold nth.
  change (2^17) with (2^16 + 2^16).
  apply Add_interval_mono3.
  apply HH.
  clear HH.
  remember (ℤ16.lst [x; x0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13;
             x14]) as t.
  clear Hbounds Hcarr1 HForalll1 Hl1 l1 Heqt.
  assert(t < 0 \/ t = 0 \/ 0 < t) by omega.
  destruct H ; [|destruct H].
  assert(getCarry 256 t <= 0).
  apply getCarry_neg_sup ; omega.
  destruct Hbound_strict.
  apply Z.le_lteq in H1.
  destruct H1.
  + apply (getCarry_incr 256) in H1.
    2: omega.
    change (getCarry 256 (38 * - 2 ^ 47)) with (-1) in H1.
    omega.
  + change (38* - 2^47) with (-5348024557502464) in H1.
    subst t; compute ; split ; intro ; tryfalse.
  + subst t ; compute ; split ; intro ; tryfalse.
  + assert(t < 2^256 \/ 2^256 <= t ) by omega.
    destruct H0.
    * replace (getCarry 256 t) with 0.
      compute ; split ; intro ; tryfalse.
      rewrite getCarry_impl_0 ; omega.
    * replace (getCarry 256 t) with 1.
      compute ; split ; intro ; tryfalse.
      change 257 with (256 + 1) in Hbound_strict.
      rewrite getCarry_1; omega.
Qed.

Theorem Zcar25519_bounds_Zlength_2:
  forall l1 l2,
    Zlength l1 = 16 ->
    Zlength l2 = 16 ->
    Forall (fun x => -2^62 < x < 2^62) l1 ->
    l2 = car25519 l1 ->
    Forall (fun x => -38 <= x < 2^16 + 38) (car25519 l2).
Proof.
move=> l1 l2 ; rewrite ?Zlength_correct => Hll1 Hll2 Hl1 Hl2;
eapply Zcar25519_bounds_length_2 ; eauto; omega.
Qed.

Lemma car25519_bound : forall l, 
  Zlength l = 16 ->
  Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) l ->
  Forall (fun x : ℤ => 0 <= x < 2 ^ 16) (car25519 (car25519 (car25519 l))).
Proof.
  intros l Hl Hb.
  eapply Zcar25519_bounds_Zlength.
  4: apply Hb.
  4: reflexivity.
  4: reflexivity.
  all: repeat apply car25519_Zlength ; assumption.
Qed.

Close Scope Z.