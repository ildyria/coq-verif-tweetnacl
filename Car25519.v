Require Export ZCarry.
Require Export Forall_ZofList.
Require Export TrippleRel.

Open Scope Z.

(*Eval simpl in (ZofList_Bound 16 16 (2 ^ 62) < 1 * 2^303).*)

Theorem Zcar25519_bounds:
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
  eapply (nth_Forall _ _ _ 0).
  intro i.
  assert(Hbounds:= Hl1).
  apply (ZofList_bounds 16 l1 16 (-2^62) (2^62)) in Hbounds.
  split ;
  [apply bounds_car_inf| apply bounds_car_sup];
  try assumption ; rewrite Hcarr2 ;
  rewrite <- ℤcar25519_eq_car25519 by assumption;
  eapply (doubleCar_ext_str (ℤ16.lst l1) _ 303) ; 
  try omega ; try (eapply le_lt_trans ; [eapply Hbounds| | ] ; compute ; reflexivity);
  try (rewrite ℤcar25519_eq_car25519 by assumption ; rewrite Hcarr1 ; reflexivity).
  compute ; auto.
  apply HForalll1.
Qed.