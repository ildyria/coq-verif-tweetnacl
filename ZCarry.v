Require Export Carry.
Import ListNotations.

Open Scope Z.

Fact lt_0_256: 0 < 2 ^ 256.
Proof. apply Z.gt_lt_iff ; apply (pown0 256) ; omega. Qed.


Fact gt_256_0: 2 ^ 256 > 0.
Proof. apply (pown0 256) ; omega. Qed.

Hint Resolve lt_0_256.
Hint Resolve gt_256_0.

(* sketch of the proof (PoC) *)
Lemma reduce_by_carry_1 :
  forall n a b,
    n > 0 ->
    a < 2 ^ n ->
    a + 1 >= 2 ^ n ->
    b = a + 1 - 2 ^ n ->
    b = 0.
Proof.
  intros n a b Hn Ha1 Ha2 Hb ; omega.
Qed.

Lemma reduce_by_carry_38 :
  forall a b,
    a < 2 ^ 16 ->
    a + 38 >= 2 ^ 16 ->
    b = a + 38 - 2 ^ 16 ->
    b < 2 ^ 16 - 38.
Proof.
  intros a b Ha1 Ha2 Hb; go.
Qed.

Lemma reduce_by_carry_38_256 :
  forall a b,
    a < 2 ^ 256 ->
    a + 38 >= 2 ^ 256 ->
    b = a + 38 - 2 ^ 256 ->
    b < 2 ^ 256 - 38.
Proof.
  intros a b Ha1 Ha2 Hb; go.
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
  intros a b Ha0 Hb0 Ha1 Ha2 Hb ; go.
Qed.

(************************************
 * START OF PROOF
 ************************************)

Lemma ZCarry25519_min_0: ℤcar25519 0 = 0.
Proof.
  reflexivity.
Qed.

Lemma ZCarry25519_min: forall x,
  0 < x -> 
  0 < ℤcar25519 x.
Proof.
  intros x Hx.
  unfold Zcar25519.
  assert(Hx_dec: {x < 2 ^ 256} + {2 ^ 256 <= x}) by apply Z_lt_le_dec.
  destruct Hx_dec; [apply Z.add_nonneg_pos | apply Z.add_pos_nonneg].
  rewrite Z.mul_comm.
  apply Zmult_gt_0_le_0_compat ; [|apply getCarry_pos] ; omega.
  apply getResidue_pos_str ; omega.
  apply Z.mul_pos_pos ; [|apply getCarry_pos_str] ; omega.
  apply getResidue_bounds ; omega.
Qed.

Lemma ZCarry25519_sup_bounds: forall x,
  x < 2 ^ 302 ->
  0 < x ->
  ℤcar25519 x < 2 ^ 257.
Proof.
  intros x Hx_supp Hx_inf.
  unfold ℤcar25519.
  change (2 ^ 257) with (2 ^ 256 + 2 ^ 256).
  apply Z.add_lt_mono.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 by omega.
  (* The idea here is to use the transitivity of < :
    a < b ->
      b < c ->
        a < c
  We therefore need to find a suitable b given here by Hbound2
  *)

  assert(H38: 38 < 2^6). (* required in the proof of Hbound2 *)
    symmetry ; go.

  assert(Hbound: x / 2 ^ 256 < 2 ^ 46). (* required in the proof of Hbound2 *)
    apply Zdiv_lt_upper_bound ; go.

  assert(Hbound2: 38 * (x / 2 ^ 256) < 2 ^ 6 * 2 ^ 46).
    apply Zmult_lt_compat.
    omega. (* uses the H38 hypothesis *)
    split.
    apply Z_div_pos ; go.
    apply Hbound. (* I could use assumption but here I need to show why we need the assert Hbound *)

  eapply Z.lt_trans.
  apply Hbound2.
  go.
  unfold getResidue.
  apply Z_mod_lt.
  auto.
Qed.

Lemma Zcarry25519_fixpoint :
  forall x, 
  0 < x < 2 ^ 256 ->
   ℤcar25519 x = x.
Proof.
  intros x Hx.
  unfold Zcar25519.
  rewrite Z.add_comm.
  rewrite Zplus_0_r_reverse.
  f_equal.
  - unfold getResidue.
    apply Zmod_small.
    split ; omega.
  - unfold getCarry.
    rewrite Z.shiftr_div_pow2 by omega.
    rewrite Z.mul_comm.
    apply Z_eq_mult.
    apply Zdiv_small ; omega.
Qed.

Fact eq_1_div256: forall a,
  2 ^ 256 <= a -> 
  a < 2 ^ 257 -> 
  a / 2 ^ 256 = 1.
Proof.
  intros a Hamin Hamax.
  assert(1 <= a / 2 ^ 256).
    rewrite <- (Z_div_same_full (2^256)).
    apply Z_div_le ; go.
    intro ; false.
  assert(a / 2 ^ 256 < 2).
    apply Z.div_lt_upper_bound ; go.
  omega.
Qed.

Lemma Zcarry25519_third :
  forall x,
   0 < x < 2 ^ 256 -> 
   2 ^ 256 <= x + 38-> 
   Zcar25519 (x + 38) < 2 ^ 16.
Proof.
  intros x Hx Hx38.
  unfold Zcar25519.
  unfold getResidue.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 by omega.

  assert(Hxmax: x + 38 < 2 ^ 257).
    change (2 ^ 257) with (2 ^ 256 + 2 ^ 256).
    apply Z.add_lt_mono ; go.

  assert(Hcarry: ((x + 38) / 2 ^ 256) = 1).
    apply eq_1_div256 ; assumption.

  assert(Hcarry38: 38 * ((x + 38) / 2 ^ 256) = 38).
    omega.

  rewrite eq_1_div256 by assumption.
  rewrite (Z.sub_lt_mono_r _ _ 38).
  rewrite <- Z.add_sub_assoc.
  rewrite Zplus_minus.
  apply (reduce_last x) ; 
  try rewrite Zmod_eq_full ; try rewrite Hcarry ; try omega.
Qed.


Lemma Zcarry25519_second : 
  forall x y,
    2 ^ 256 <= x < 2 ^ 257 ->
    y + 38 = Zcar25519 x ->
    y < 2^256.
Proof.
  intros x y Hx Hy.
  unfold Zcar25519 in Hy.
  unfold getCarry in Hy.
  unfold getResidue in Hy.
  rewrite Z.shiftr_div_pow2 in Hy by omega.
  rewrite eq_1_div256 in Hy by omega.
  rewrite <- Zred_factor0 in Hy.
  rewrite Z.add_comm in Hy.
  rewrite Z.add_cancel_l in Hy.
  subst y.
  apply Z.mod_pos_bound.
  auto.
Qed.

Lemma doubleCar:
  forall x y,
   0 <= x < 2 ^ 302 ->
   y = Zcar25519 x ->
   Zcar25519 y < 2 ^ 256.
Proof.
  intros x y Hx Hy.
  assert(Hx_dec: x = 0 \/ 0 < x < 2^256 \/ 2 ^ 256 <= x) by omega.
  case Hx_dec ; clear Hx_dec ; intro Hx_dec.
    {
      (* case x = 0 *)
      go.
    }
  case Hx_dec ; clear Hx_dec ; intro Hx_dec.
    {
      (* case  0 < x < 2^256 *)
      rewrite Zcarry25519_fixpoint in Hy by omega.
      subst y.
      rewrite Zcarry25519_fixpoint ; omega.
    }
    {
      (* case  2^256 <= x *)
      assert(Hy_min: 0 < y).
        subst y.
        apply ZCarry25519_min.
        eapply (Z.lt_le_trans _ (2^256) _) ; go.

      assert(Hy_max: y < 2 ^ 257).
        subst y.
        apply ZCarry25519_sup_bounds ; go.
        apply Z_le_lt_eq_dec in Hx_dec.
        destruct Hx_dec.
        eapply Z.lt_trans.
        apply Z.gt_lt_iff.
        apply (pown0 256). 
        omega.
        assumption.
        subst x.
        apply Z.gt_lt_iff.
        apply (pown0 256).
        omega.

    assert(Hy_dec: 0 < y < 2^256 \/ 2 ^ 256 <= y) by omega.
    case Hy_dec ; clear Hy_dec ; intro Hy_dec.
      {
        rewrite Zcarry25519_fixpoint ; omega.
      }
      {
        unfold Zcar25519.
        unfold Zcar25519 in Hy.
        unfold getCarry in Hy.
        unfold getCarry.
        unfold getResidue in Hy.
        unfold getResidue.
        rewrite Z.shiftr_div_pow2 in Hy by omega.
        rename y into t.
        assert(Hy_t: exists y, t = 2^256 + y) by (exists (t - 2^256) ; omega).
        destruct Hy_t as [y Hy_t].
        rewrite Hy_t.
        rewrite Z.shiftr_div_pow2; [|omega].
        assert(Hcarry: ((2^256 + y) / 2 ^ 256) = 1).
          apply eq_1_div256 ; omega.
        rewrite Hcarry.
        change (38 * 1) with 38.
        clear Hcarry.
        rewrite Hy_t in Hy.
        subst t.
        change(2 ^ 257) with (2 ^ 256 + 2 ^ 256) in Hy_max.
        apply Zplus_lt_reg_l in Hy_max.
        assert(Hy_tempval: (1 * 2 ^ 256 + y) mod 2 ^ 256 = y).
          rewrite Z.add_comm.
          rewrite Z_mod_plus_full.
          rewrite Zmod_small ; try reflexivity ; omega.
          change (1 * 2 ^256) with (2 ^256) in Hy_tempval.
        rewrite Hy_tempval.
        clear Hy_min.
        assert(Hy_min: 0 <= y) by omega.
        clear Hy_dec.
        clear Hy_tempval.
        symmetry in Hy.
        apply Zplus_minus_eq in Hy.
        subst.
        assert(x mod 2 ^ 256 < 2 ^ 256).
        apply Z_mod_lt ; omega.
        rewrite <- Z.lt_sub_0 in H.
        assert(x / 2 ^ 256 < 2^46).
        apply Z.div_lt_upper_bound ; try omega.
        change (2 ^ 256 * 2 ^ 46) with (2 ^ 302).
        omega.
        assert(38 * (x / 2 ^ 256) + x mod 2 ^ 256 - 2 ^ 256 < 38 * 2^46).
        omega.
        assert(38 + (38 * (x / 2 ^ 256) + x mod 2 ^ 256 - 2 ^ 256) < 38 + 38 * 2^46).
        omega.
        assert(38 + 38 * 2 ^ 46 < 2^256).
        compute ; reflexivity.
        omega.
      }
    }
Qed.

Lemma trippleCar:
  forall x y z,
   0 <= x < 2 ^ 302 ->
   y = Zcar25519 x ->
   z = Zcar25519 y ->
   Zcar25519 z < 2 ^ 256.
Proof.
  intros x y z Hx Hy Hz.
  assert(Hx_dec: x = 0 \/ 0 < x < 2^256 \/ 2 ^ 256 <= x) by omega.
  case Hx_dec ; clear Hx_dec ; intro Hx_dec.
    {
      (* case x = 0 *)
      go.
    }
  case Hx_dec ; clear Hx_dec ; intro Hx_dec.
    {
      (* case  0 < x < 2^256 *)
      rewrite Zcarry25519_fixpoint in Hy by omega.
      subst y.
      rewrite Zcarry25519_fixpoint in Hz by omega.
      subst z.
      rewrite Zcarry25519_fixpoint ; omega.
    }
    {
      (* case  2^256 <= x *)
      assert(Hy_min: 0 < y).
        subst y.
        apply ZCarry25519_min.
        eapply (Z.lt_le_trans _ (2^256) _) ; go.

      assert(Hz_min: 0 < z).
        subst z.
        apply ZCarry25519_min. go.

      assert(Hy_max: y < 2 ^ 257).
        subst y.
        apply ZCarry25519_sup_bounds ; go.
        apply Z_le_lt_eq_dec in Hx_dec.
        destruct Hx_dec.
        eapply Z.lt_trans.
        apply Z.gt_lt_iff.
        apply (pown0 256). 
        omega.
        assumption.
        subst x.
        apply Z.gt_lt_iff.
        apply (pown0 256).
        omega.

      assert(Hz_max: z < 2 ^ 257).
        subst z.
        apply ZCarry25519_sup_bounds ; go.
        apply Z_le_lt_eq_dec in Hx_dec.
        destruct Hx_dec.
        eapply Z.lt_trans.
        eapply Hy_max.
        compute ; reflexivity.
        eapply Z.lt_trans.
        eapply Hy_max.
        go.

    assert(Hy_dec: 0 < y < 2^256 \/ 2 ^ 256 <= y) by omega.
    case Hy_dec ; clear Hy_dec ; intro Hy_dec.
      {
        (* case y < 2 ^ 256 *)
        rewrite Zcarry25519_fixpoint in Hz by omega.
        subst z.
        rewrite Zcarry25519_fixpoint ; omega.
      }
      { 
        assert(z < 2 ^ 256).
        subst z.
        eapply doubleCar.
        eauto.
        eauto.
        rewrite Zcarry25519_fixpoint ; go.
      }
    }
Qed.
