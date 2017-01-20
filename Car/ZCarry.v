Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Car.Reduce.
Require Import Tweetnacl.Car.Carry.
Require Import Prelude.prelude.prelude.
Require Import Nsatz.
Require Import Psatz.

Open Scope Z.

Ltac getCarryToZ := 
  unfold getCarry in *; try rewrite Z.shiftr_div_pow2 in * by omega.

Ltac getResidueToZ := 
  unfold getResidue in *; getCarryToZ ; 
  try rewrite Z.shiftl_mul_pow2 in * by omega.

Ltac ZCar25519ToZ := 
  unfold Zcar25519 in *;
  getResidueToZ.

Fact lt_0_256: 0 < 2 ^ 256.
Proof. reflexivity. Qed.

Fact gt_256_0: 2 ^ 256 > 0.
Proof. reflexivity. Qed.

Fact pow2256val : 2 ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. reflexivity. Qed.

Hint Resolve lt_0_256.
Hint Resolve gt_256_0.
Hint Resolve pow2256val.

(************************************
 * START OF PROOF
 ************************************)

Lemma ZCarry25519_of_0: ℤcar25519 0 = 0.
Proof. reflexivity. Qed.

Lemma ZCarry25519_pos: forall x,
  0 <= x -> 
  0 <= ℤcar25519 x.
Proof.
  repeat match goal with
    | _ => progress intros
    | _ => progress unfold Zcar25519
    | _ => progress apply getCarry_pos
    | _ => progress apply getResidue_bounds
    | _ => progress apply OMEGA2
    | _ => omega
    | _ => (rewrite Z.mul_comm ; apply Zmult_gt_0_le_0_compat)
  end.
Qed.

Lemma ZCarry25519_neg_str: forall x m,
   256 <= m < 512 ->
  -2^m < x ->
  x < 0 ->
  38*-2^(m - 256) <= ℤcar25519 x < 2^256.
Proof.
  intros x m Hm Hxmin Hxmax.
  unfold Zcar25519.
  getCarryToZ.
  replace (38 * - 2 ^ (m - 256)) with (38 * - 2 ^ (m - 256) + 0) by omega.
  split.
  apply Z.add_le_mono.
  apply Zmult_le_compat_l ; try omega.
  assert(H256: - (2 ^ m / 2 ^ 256) = - 2 ^ (m - 256)).
    rewrite Z.pow_sub_r ; try omega.
  rewrite <- H256.
  rewrite <- Z_div_zero_opp_full.
  apply Z_div_le ; auto ; omega.
  replace (2 ^ m) with (2 ^ (m - 256) * 2 ^256).
  apply Z_mod_mult.
  rewrite <- Zpower_exp ; try omega.
  f_equal ; omega.
  apply getResidue_bounds ; omega.
  assert(Hs: 38 * (x / 2 ^ 256) + x mod 2 ^ 256 < 38 * (x / 2 ^ 256) + 2 ^ 256).
    apply Zplus_lt_compat_l.
    apply Z_mod_lt.
    reflexivity.
  assert(38 * (x / 2 ^ 256) + 2 ^ 256 < 2 ^ 256).
    clear Hs.
    apply (Z.le_lt_add_lt (-2^256) (-2^256)).
    reflexivity.
    rewrite Zplus_assoc_reverse.
    change (2 ^ 256 + - 2 ^ 256) with 0.
    assert(x / 2 ^ 256 <= -1).
      assert(Hx: x <= -2^256 \/ -2^256 < x) by omega.
      destruct Hx.
      apply Zdiv_le_upper_bound.
      compute ; reflexivity.
      omega.
      pose(r := x + 2 ^ 256).
      rewrite Z.lt_eq_cases.
      right.
      symmetry.
      apply (Zdiv_unique x (2^256) (-1) r).
      subst r ; omega.
      subst r ; omega.
    omega.
    rewrite getResidue_mod_eq by omega.
    unfold getResidue_mod.
  omega.
Qed.

Lemma ZCarry25519_sup_bounds_str: forall x m,
  256 <= m < 506 ->
  x < 2 ^ m ->
  0 < x ->
  ℤcar25519 x < 2 ^ 257.
Proof.
  assert(H38: 38 < 2^6) by reflexivity. (* required in the proof of Hbound2 *)

  repeat match goal with
    | _ => omega
    | _ => f_equal ; omega
    | _ => progress intros
    | _ => progress unfold Zcar25519
    | _ => progress getCarryToZ
    | _ => progress change (2 ^ 257) with (2 ^ 256 + 2 ^ 256)
    | _ => progress apply Z.add_lt_mono
    | _ => progress apply getResidue_bounds
  end.
  (* The idea here is to use the transitivity of < :
    a < b ->
      b < c ->
        a < c
  We therefore need to find a suitable b given here by Hbound2
  *)

  assert(Hbound: x / 2 ^ 256 < 2 ^ (m - 256)). (* required in the proof of Hbound2 *)
    apply Zdiv_lt_upper_bound; auto.
    replace (2 ^ (m - 256) * 2 ^ 256) with (2^m).
    omega.
    rewrite <- Zpower_exp ; try omega.
    f_equal ; omega.

  assert(Hbound2: 38 * (x / 2 ^ 256) < 2 ^ 6 * 2 ^ (m - 256)).
    apply Zmult_lt_compat.
    omega. (* uses the H38 hypothesis *)
    split.
    apply Z_div_pos ; go.
    apply Hbound. (* I could use assumption but here I need to show why we need the assert Hbound *)

  eapply Z.lt_le_trans.
  apply Hbound2.
  rewrite <- Zpower_exp ; try omega.
  apply Z.pow_le_mono_r ; omega.
Qed.

Lemma ZCarry25519_sup_bounds_str2: forall x m,
  256 <= m < 506 ->
  x < 2 ^ m ->
  0 < x ->
  ℤcar25519 x < 2 ^ 256 - 38 + 2 ^ 256.
Proof.
  intros.
  unfold Zcar25519.
  assert(H': getResidue 256 x < 2 ^ 256).
    apply getResidue_bounds ; omega.
  remember (getResidue 256 x) as y.
  remember (getCarry 256 x) as z.
  getCarryToZ.
  assert(H'': z < 2^250).
  subst z.
  apply Zdiv_lt_upper_bound ; auto.
  rewrite <- Z.pow_add_r by omega.
  change (250 + 256) with 506.
  eapply Z.lt_trans; eauto.
  apply Z.pow_lt_mono_r ; try omega.
  lia.
Qed.

Lemma ZCarry25519_sup_bounds_str3: forall x m,
  256 <= m < 506 ->
  0 <= x < 2 ^ m ->
  ℤcar25519 x < 2 ^ 256 - 38 + 2 ^ 256.
Proof.
  intros.
  unfold Zcar25519.
  assert(H': getResidue 256 x < 2 ^ 256).
    apply getResidue_bounds ; omega.
  remember (getResidue 256 x) as y.
  remember (getCarry 256 x) as z.
  getCarryToZ.
  assert(H'': z < 2^250).
  subst z.
  apply Zdiv_lt_upper_bound ; auto.
  rewrite <- Z.pow_add_r by omega.
  change (250 + 256) with 506.
  eapply Z.lt_trans. eapply H0.
  apply Z.pow_lt_mono_r ; try omega.
  lia.
Qed.


Lemma ZCarry25519_sup_bounds: forall x,
  x < 2 ^ 302 ->
  0 < x ->
  ℤcar25519 x < 2 ^ 257.
Proof.
  intros x Hx_supp Hx_inf.
  apply (ZCarry25519_sup_bounds_str x 302) ; omega.
Qed.

Lemma Zcarry25519_fixpoint :
  forall x, 
  0 <= x < 2 ^ 256 ->
   ℤcar25519 x = x.
Proof.
  repeat match goal with
    | _ => omega
    | _ => progress intros
    | _ => progress unfold Zcar25519 ; getCarryToZ
    | [ |- _ + _ = _ ] =>  rewrite Z.add_comm ;  rewrite Zplus_0_r_reverse ;  f_equal
    | _ => progress rewrite getResidue_mod_eq ; unfold getResidue_mod
    | _ => progress apply Zmod_small
    | _ => rewrite Z.mul_comm ; apply Z_eq_mult ; apply Zdiv_small ; omega
  end.
Qed.

Fact lower_eq_256: forall a,
  2 ^ 256 <= a -> 
  a < 2 ^ 257 -> 
  1 <= a / 2 ^ 256.
Proof.
  intros.
  rewrite <- (Z_div_same_full (2^256)).
  apply Z_div_le ; go.
  intro; false.
Qed.

Fact upper_eq_256: forall a,
  2 ^ 256 <= a -> 
  a < 2 ^ 257 -> 
  a / 2 ^ 256 < 2.
Proof.
  intros ; apply Z.div_lt_upper_bound ; go.
Qed.

Fact eq1 : forall a, a = 1 <-> a < 2 /\ 1 <= a.
Proof. intros. omega. Qed.

Fact eq_1_div256: forall a,
  2 ^ 256 <= a -> 
  a < 2 ^ 257 -> 
  a / 2 ^ 256 = 1.
Proof.
  repeat match goal with 
  | _ => progress intros
  | _ => assumption
  | [ |- _ < 2 ] => apply upper_eq_256
  | [ |- 1 <= _ ] => apply lower_eq_256
  | [ |- _ /\ _ ]  => progress split
  | _ => progress apply eq1
  end.
Qed.
(* in the previous proof the order of the tactics matter !
  if apply eq1 is before split : infinite loop *)

Lemma getCarryNeg:
  forall x,
    - 2 ^ 250 < x < 0 -> 
    getCarry 256 x = -1.
Proof.
  repeat match goal with
    | _ => omega
    | _ => progress intros
    | _ => progress getCarryToZ
    | [ |- _ = -1 ] => symmetry
    | [ |- context[?x/2^256] ] => progress apply (Z.div_unique_pos _ (2^256) (-1) (x + 2 ^ 256))
    | [ H : _ /\ _ |- _ ] => progress destruct H
    | [ |- _ /\ _ ] => progress split
  end.
  assert(2^256 - 2 ^ 250 < x + 2 ^ 256). omega.
  simpl in * ; omega.
Qed.

Lemma sndCar_neg_str: 
  forall x,
   -2^250 < x < 0 ->
   0 <= Zcar25519 x < 2 ^ 256.
Proof.
  intros x Hx.
  unfold Zcar25519.
  rewrite (getCarryNeg x Hx).
  rewrite getResidue_mod_eq by omega.
  unfold getResidue_mod.
  rewrite <- (Z_mod_plus_full x 1 (2^256)).
  replace ((x + 1 * 2 ^ 256) mod 2 ^ 256) with (x + 1 * 2 ^ 256).
  replace (38 * -1 + (x + 1 * 2 ^ 256)) with (2 ^ 256 - 38 + x).

  assert(2 ^ 256 - 38 - 2^250 < 2 ^ 256 - 38 + x) by omega.
  simpl (2 ^ 256 - 38 - 2 ^ 250 ) in H.
  omega.
  omega.
  symmetry.
  apply Zmod_small.

  assert(2^256 - 2 ^ 250 < x + 2 ^ 256) by omega.
  rewrite Z.mul_comm.
  rewrite <- Zred_factor0.
  simpl in *.
  omega.
Qed.

Lemma sndCar_neg: 
  forall x,
   -2^52 < x < 0 ->
   0 <= Zcar25519 x < 2 ^ 256.
Proof.
  intros x Hx.
  apply sndCar_neg_str.
  change (-2^250) with (-1809251394333065553493296640760748560207343510400633813116524750123642650624).
  change (-2^52) with (-4503599627370496) in Hx.
  omega.
Qed.

Lemma secondIterCar: 
  forall x,
    2 ^256 <= x ->
    x < 2 ^ 256 - 38 + 2 ^ 256 ->
    Zcar25519 x < 2 ^ 256.
Proof.
  assert(0 < 2^256 ) by reflexivity.
  assert(2 ^ 256 - 38 + 2 ^ 256 < 2 ^ 257) by Psatz.nia.
  repeat match goal with
    | _ => progress intros
    | _ => progress unfold Zcar25519
    | _ => progress unfold getResidue
    | _ => progress unfold getCarry
    | _ => progress rewrite Z.shiftl_mul_pow2 by omega
    | _ => progress rewrite Z.shiftr_div_pow2 by omega
    | [  |- context[?x/2^256] ] => progress rewrite (eq_1_div256 x) ; try omega
  end.
Qed.

Lemma doubleCar_str_case:
  forall x y m,
   256 <= m < 506 ->
   2^256 <= x < 2 ^ m ->
   y = Zcar25519 x ->
   2^256 <= y ->
   Zcar25519 y < 2 ^ 256.
Proof.
  assert(0 < 2^256 ) by reflexivity.
  repeat match goal with
    | _ => progress intros 
    | _ => progress apply secondIterCar
    | _ => assumption
    | _ => progress subst
    | _ => eapply ZCarry25519_sup_bounds_str2 ; go
    end.
Qed.

Lemma doubleCar_str:
  forall x y m,
   256 <= m < 506 ->
   0 <= x < 2 ^ m ->
   y = Zcar25519 x ->
   Zcar25519 y < 2 ^ 256.
Proof.
(*Print Zcar25519. Print getCarry.*)
  intros x y m Hm Hx Hy.
  assert(Hx_dec: x = 0 \/ 0 < x < 2^256 \/ 2 ^ 256 <= x) by omega.
  assert(Hy_dec: y < 0 \/ 0 <= y < 2^256 \/ 2 ^ 256 <= y) by omega.
  repeat match goal with
         | [ H : _ \/ _ |- _ ] => destruct H
         | _ => progress go
         | _ => progress subst
         | [ H : context[ℤcar25519 _] |- _ ] => rewrite Zcarry25519_fixpoint in H by omega
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : ℤcar25519 ?x < 0, H1 : 0 <= ?x |- _ ] => apply ZCarry25519_pos in H1 ; omega
         | [  |- context[ℤcar25519 ?x] ] => rewrite (Zcarry25519_fixpoint x) by omega
         | _ => progress eauto using doubleCar_str_case
         end.
Qed.

Lemma doubleCar:
  forall x y,
   0 <= x < 2 ^ 302 ->
   y = Zcar25519 x ->
   Zcar25519 y < 2 ^ 256.
Proof.
  intros ; apply (doubleCar_str x _ 302) ; go.
Qed.

Lemma doubleCar_ext_str: forall x y m,
  256 <= m < 500 ->
  -2^m < x < 2^m ->
  y = Zcar25519 x ->
   0 <= Zcar25519 y < 2 ^ 256.
Proof.
  intros x y m Hm Hx Hy.
  assert(Hx_dec: -2^m < x < 0 \/ 0 <= x < 2^m) by omega.
  case Hx_dec ; clear Hx_dec ; intro Hx_dec.
    {
      assert(38*-2^(m - 256) <= ℤcar25519 x < 2^256).
      apply ZCarry25519_neg_str ; omega.
      assert(HZcar_dec: ℤcar25519 x < 0 \/ 0 <= ℤcar25519 x) by omega.
      destruct HZcar_dec.
      - apply sndCar_neg_str.
        subst y.
        destruct H.
        split ; try omega.
        eapply (Z.lt_le_trans _ (38 * - 2 ^ (m - 256))) ; try omega.
        rewrite Z.mul_opp_r.
        rewrite <- Z.opp_lt_mono.
        eapply (Z.lt_le_trans _ (2^6 * 2^(m - 256))).
        apply Zmult_gt_0_lt_compat_r.
        rewrite Z.gt_lt_iff.
        apply Z.pow_pos_nonneg; omega.
        compute ; reflexivity.
        rewrite <- Z.pow_add_r ; try omega.
        apply Z.pow_le_mono_r; omega.
      - rewrite Zcarry25519_fixpoint ; subst y.
        omega.
        omega.
    }
  split.
  apply ZCarry25519_pos.
  subst y.
  apply ZCarry25519_pos.
  omega.
  eapply doubleCar_str ; eauto.
  omega.
Qed.


Lemma doubleCar_ext:
  forall x y,
   -2^302 < x < 2 ^ 302 ->
   y = Zcar25519 x ->
   0 <= Zcar25519 y < 2 ^ 256.
Proof.
  intros x y Hx Hy ; eapply (doubleCar_ext_str _ _ 302) ; go.
Qed.

Lemma trippleCar:
  forall x y z,
   0 <= x < 2 ^ 302 ->
   y = Zcar25519 x ->
   z = Zcar25519 y ->
   Zcar25519 z < 2 ^ 256.
Proof.
  intros ; subst.
  rewrite Zcarry25519_fixpoint ; try eapply doubleCar ; eauto.
  split.
  repeat apply ZCarry25519_pos ; omega.
  eapply doubleCar ; eauto.
Qed.
