From Tweetnacl Require Import Libs.Export.

Open Scope Z.

(*Notation "A :𝓖𝓕" := (A mod (2^255 - 19)) (at level 80, right associativity).*)

Lemma t2256is38 : (2^256 :𝓖𝓕 ) = (38 :𝓖𝓕).
Proof.
  compute ; reflexivity.
Qed.

Lemma Zshiftr_div_pow2_16: forall a : Z, Z.shiftr a 16 = a / 2 ^ 16.
Proof. intro a ; apply Z.shiftr_div_pow2 ; omega. Qed.

Fact factors_256: (2 ^ 256) = (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 *
(2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16 * (2 ^ 16)))))))))))))))).
Proof. compute ; reflexivity. Qed.

Definition reduce256 n := 
  let c := n / 2^(256) in
  n + 38 * c - 2^(256) * c.

Lemma reduceGF : forall m, (reduce256 m :𝓖𝓕) = (m :𝓖𝓕).
Proof.
  intro m.
  unfold reduce256.
  rewrite Zminus_mod.
  rewrite Zplus_mod.
  rewrite <- Zmult_mod_idemp_l.
  rewrite <- t2256is38.
  rewrite Zminus_mod_idemp_l.
  rewrite Zmult_mod_idemp_l.
  rewrite <- Z.add_sub_assoc.
  rewrite <- Zminus_diag_reverse.
  rewrite <- Zplus_0_r_reverse.
  rewrite Zmod_mod.
  reflexivity.
Qed.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma res_pos: forall (a:Z), 0 <= a - Z.shiftl (Z.shiftr a n) n.
Proof.
  intro a.
  orewrite Z.shiftr_div_pow2.
  orewrite Z.shiftl_mul_pow2.
  apply Zle_minus_le_0.
  rewrite Z.mul_comm.
  apply Z.mul_div_le.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
Qed.

Definition getCarry (m:Z) : Z :=  Z.shiftr m n.

Definition getResidue (m:Z) : Z := m - Z.shiftl (getCarry m) n.

Definition getResidue_mod (m:Z) : Z := m mod 2^n.

Lemma getResidue_mod_eq: forall (m:Z), getResidue m = getResidue_mod m.
Proof.
  intro a.
  symmetry.
  unfold getResidue.
  unfold getResidue_mod.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  orewrite Z.shiftl_mul_pow2.
  apply Zplus_minus_eq.
  rewrite Z.mul_comm.
  apply Z_div_mod_eq.
  apply pown0.
  assumption.
Qed.

Lemma getResidue_0 : getResidue 0 = 0.
Proof. rewrite getResidue_mod_eq; go. Qed.

Lemma getCarry_0 : getCarry 0 = 0.
Proof. apply Z.shiftr_0_l. Qed.

Lemma getResidue_bounds : forall m:Z, 0 <= getResidue m < 2^n.
Proof.
  intro m.
  rewrite getResidue_mod_eq.
  unfold getResidue_mod.
  apply Z_mod_lt.
  apply pown0.
  assumption.
Qed.

Lemma mod_div: forall m:Z, m mod 2 ^ n + 2 ^ n * (m / 2 ^ n) = m.
Proof.
  intro.
  rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq.
  apply pown0.
  assumption.
Qed.

Lemma residuteCarry: forall m:Z, getResidue m + 2^n *getCarry m = m.
Proof.
  intro m.
  unfold getResidue.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  orewrite Z.shiftl_mul_pow2.
  rewrite Z.mul_comm.
  omega.
Qed.

Lemma getCarryMonotone_pos: forall m,
  0 < m ->
    getCarry m < m.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  induction m ; go.
  - apply Z_div_lt ; go.
  assert(2 = 2 ^ 1) by go.
  rewrite {2}H; clear H.
  rewrite Z.ge_le_iff.
  apply Z.pow_le_mono_r_iff ; omega.
  - assert (Z.neg p < 0) by apply Zlt_neg_0 ; go.
Qed.

Lemma getCarryMonotone_neg: forall m,
  m < 0 -> 
    m <= getCarry m.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  induction m.
  go.
  - assert (Z.pos p > 0) by apply Zgt_pos_0 ; go.
  - apply Zdiv_le_lower_bound.
    rewrite <- Z.gt_lt_iff ; apply pown0 ; assumption.
    rewrite Z.mul_comm.
    apply le_mul_neg ; try assumption.
    assert(Hnn:= pown n Hn).
    omega.
Qed.

Lemma getResidue_pos_str: forall m,
  0 < m < 2^n ->
    0 < getResidue m < 2^n.
Proof.
  intros m Hm.
  rewrite getResidue_mod_eq.
  unfold getResidue_mod.
  rewrite Z.mod_small ; omega.
Qed.

Lemma getCarry_pos: forall m,
  0 <= m ->
  0 <= getCarry m.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  apply Z.div_pos.
  assumption.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
Qed.

Lemma getCarry_pos_str: forall m,
  2 ^ n <= m ->
  0 < getCarry m.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  apply Z.div_str_pos.
  split.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
  assumption.
Qed.

Lemma getCarry_impl_0: forall m,
  0 <= m < 2^n ->
    getCarry m = 0.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  symmetry.
  eapply Zdiv_unique.
  eapply Hm.
  omega.
Qed.

Lemma getCarry_1: forall m,
  2^n <= m < 2^(n+1) ->
  getCarry m = 1.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  assert(1<= m / 2 ^ n).
  replace 1 with (2 ^ n/2 ^ n) by (apply Z_div_same_full; intro ; assert(Ht:= pown0 n Hn) ; omega).
  apply Z_div_le.
  apply pown0 ; auto.
  omega.
  assert(m / 2 ^ n < 2).
  apply Z.div_lt_upper_bound.
  assert(Hnn := pown0 n Hn) ; omega.
  rewrite Z.mul_comm.
  rewrite <- Z.pow_succ_r.
  destruct Hm.
  rewrite <- Z.add_1_r.
  assumption.
  omega.
  omega.
Qed.

Lemma getCarry_neg_sup: forall m,
  m < 0 -> 
    getCarry m <= 0.
Proof.
  intros m Hm.
  unfold getCarry.
  orewrite Z.shiftr_div_pow2.
  replace 0 with (0 / 2^n).
  apply Z_div_le.
  apply pown0 ; auto.
  omega.
  apply Zdiv_small.
  split.
  reflexivity.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
Qed.

Lemma getCarryMonotone_pos_le: forall m,
  0 <= m ->
    getCarry m <= m.
Proof.
  intros m Hm.
  apply Zle_lt_or_eq in Hm.
  destruct Hm.
  apply getCarryMonotone_pos in H.
  omega.
  subst.
  rewrite getCarry_0 ; reflexivity.
Qed.

Lemma getCarry_bounds: forall x m,
  -2 ^ m < x < 2 ^ m -> 
    -2 ^ m <= getCarry x <= 2 ^ m.
Proof.
  intros.
  assert(x < 0 \/ x >= 0) by omega.
  destruct H0.
  assert(Hx:= getCarry_neg_sup x  H0).
  assert(Hxx:= getCarryMonotone_neg x H0).
  omega.
  move: H0 ; rewrite Z.ge_le_iff => H0.
  assert(Hx := getCarry_pos x H0).
  assert(Hxx := getCarryMonotone_pos_le x H0).
  omega.
Qed.

Lemma getCarry_incr : forall x y,
  x < y -> getCarry x <= getCarry y.
Proof.
  intros.
  unfold getCarry.
  repeat orewrite Z.shiftr_div_pow2.
  apply Z_div_le.
  apply pown0.
  assumption.
  omega.
Qed.
End Integer.

Lemma getCarry_bound_str63 : forall x,
  - 2^63 < x < 2^63 -> -2^62 < getCarry 16 x < 2^62.
Proof.
  intros.
  assert(Hbound: getCarry 16 (- 2^63) <= getCarry 16 x <= getCarry 16 (2^63)).
  split ; apply getCarry_incr ; omega.
  change (getCarry 16 (- 2 ^ 63)) with (-140737488355328) in Hbound;
  change (getCarry 16 (2 ^ 63)) with (140737488355328) in Hbound.
  assert(-2^62 < -140737488355328) by reflexivity.
  assert(140737488355328 < 2 ^62) by reflexivity.
  omega.
Qed.

Lemma getCarry_bound_str47 : forall x,
  - 2^63 < x < 2^63 -> -2^47 <= getCarry 16 x <= 2^47.
Proof.
  intros.
  assert(Hbound: getCarry 16 (- 2^63) <= getCarry 16 x <= getCarry 16 (2^63)).
  split ; apply getCarry_incr ; omega.
  change (getCarry 16 (- 2 ^ 63)) with (-140737488355328) in Hbound;
  change (getCarry 16 (2 ^ 63)) with (140737488355328) in Hbound.
  change (-2 ^ 47) with (-140737488355328).
  change (2 ^ 47) with (140737488355328).
  omega.
Qed.

Close Scope Z.