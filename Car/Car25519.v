Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Car.Carry.
Require Import Tweetnacl.Car.ZCarry.
Require Import Tweetnacl.Car.Reduce.
Require Import stdpp.prelude.

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
  try (rewrite ℤcar25519_eq_car25519_length by auto ; try rewrite Hcarr1 ; reflexivity).
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
  try (rewrite ℤcar25519_eq_car25519_Zlength by auto ; try rewrite Hcarr1 ; reflexivity).
Qed.
