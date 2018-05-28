Require Export Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z.

Lemma and_0_or_1 : forall a , 0 <= Z.land a 1 <= 1.
Proof. intros [|[]|[|[]|]] ; cbv ; split ; discriminate. Qed.

Lemma Zred_factor6 : forall m n, (1 + m) * n = n + n * m.
Proof. intros ; Psatz.nia. Qed.

Lemma Zred_factor7 : forall m n, (1 + m) * n = n + m * n.
Proof. intros ; Psatz.nia. Qed.

Lemma Zred_factor8: forall n m p : Z, m * n + p * n = (m + p) * n.
Proof. intros ; Psatz.nia. Qed.

Fact le_mul_neg : forall m n,  m < 0 ->  1 <= n ->  n * m <= m.
Proof. intros m n Hm Hn. Psatz.nia. Qed.

Fact le_mul_pos : forall m n, 0 < m -> 1 <= n -> m <= n * m.
Proof. intros m n Hm Hn. Psatz.nia. Qed.

Lemma le_mul_neg_le: forall m n : Z, m <= 0 -> 1 <= n -> n * m <= m.
Proof. intros m n Hm Hn. Psatz.nia. Qed.

Fact le_mul_pos_le : forall m n, 0 <= m -> 1 <= n -> m <= n * m.
Proof. intros m n Hm Hn. Psatz.nia. Qed.

Definition min_prod (min1 max1 min2 max2: Z) : Z:=
  Z.min (Z.min (min1*min2) (max1*max2)) (Z.min (max1*min2) (min1*max2)).

Definition max_prod (min1 max1 min2 max2: Z) : Z:=
  Z.max (Z.max (min1*min2) (max1*max2)) (Z.max (max1*min2) (min1*max2)).

Lemma min_prod_neg_lt : forall a b c d,
  a < 0 < b ->
  c < 0 < d ->
  min_prod a b c d < 0.
Proof.
    intros. unfold min_prod.
    repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma min_prod_neg_le : forall a b c d,
  a <= 0 <= b ->
  c <= 0 <= d ->
  min_prod a b c d <= 0.
Proof.
    intros. unfold min_prod.
    repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma max_prod_pos_lt : forall a b c d,
  a < 0 < b ->
  c < 0 < d ->
  0 < max_prod a b c d.
Proof.
    intros. unfold max_prod.
    repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma max_prod_pos_le : forall a b c d,
  a <= 0 <= b ->
  c <= 0 <= d ->
  0 <= max_prod a b c d.
Proof.
    intros. unfold max_prod.
    repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma Mult_interval_correct_min_max_lt :
  forall a b c d x y : Z,
    a < x < b ->
    c < y < d ->
    min_prod a b c d < x * y < max_prod a b c d.
Proof.
  intros. unfold min_prod. unfold max_prod. split.
  repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
  repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma Mult_interval_correct_min_max_le :
  forall a b c d x y : Z,
    a <= x <= b ->
    c <= y <= d ->
    min_prod a b c d <= x * y <= max_prod a b c d.
Proof.
  intros. unfold min_prod. unfold max_prod. split.
  repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
  repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases a), (Z.nonpos_pos_cases b);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma Mult_interval_correct_pos :
  forall c d x y : Z,
    0 < x ->
    c < y < d ->
    x * c < x * y < x * d.
Proof.
  intros. split.
  repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
  repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma Mult_interval_correct_pos_le :
  forall c d x y : Z,
    0 < x ->
    c <= y <= d ->
    x * c <= x * y <= x * d.
Proof.
  intros. split.
  repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
  repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma Mult_interval_correct_nonpos :
  forall c d x y : Z,
    x < 0 ->
    c < y < d ->
    x * d < x * y < x * c.
Proof.
  intros. split.
  repeat apply Z.min_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
  repeat apply Z.max_case_strong;
    destruct (Z.nonpos_pos_cases x), (Z.nonpos_pos_cases y);
    destruct (Z.nonpos_pos_cases c), (Z.nonpos_pos_cases c);
    Psatz.nia.
Qed.

Lemma Add_interval_mono:
  forall a b c d x y: Z,
  a < x < b ->
  c < y < d ->
  a + c < x + y < b + d.
Proof. intros ; split ; apply Z.add_lt_mono ; omega. Qed.

Lemma Add_interval_mono2:
  forall b c d x y: Z,
  0 <= x < b ->
  c < y < d ->
  c < x + y < b + d.
Proof. intros; change c with (0 + c) ; split ;[apply Z.add_le_lt_mono | apply Z.add_lt_mono] ; omega. Qed.

Lemma Add_interval_mono3:
  forall b c d x y: Z,
  0 <= x < b ->
  c <= y <= d ->
  c <= x + y < b + d.
Proof. intros; change c with (0 + c) ; split ;[apply Z.add_le_mono | apply Z.add_lt_le_mono] ; omega. Qed.

Lemma div_interval_mono:
  forall a b c x: Z,
  0 < c ->
  a <= x <= b ->
  a / c <= x / c <= b / c.
Proof. intros ; split ; apply Z_div_le ; omega. Qed.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma pown: 2 ^ n > 1.
Proof. rewrite Z.gt_lt_iff ; apply Z.pow_gt_1 ; omega. Qed.

Lemma pown0: 2 ^ n > 0.
Proof. assert(Hp:= pown) ; omega. Qed.

Lemma pown2: 2 <= 2 ^ n.
Proof. change 2 with (2 ^ 1) ;apply Z.pow_le_mono ; change (2^1) with 2 ; omega. Qed.

Lemma bound_pow_add: forall a b : Z,
  a < 2^n -> b < 2^n ->
    a + b < 2^Z.succ n.
Proof.
  intros.
  assert(H': 2 ^ Z.succ n = 2 * 2 ^ n) by (apply Z.pow_succ_r ; omega).
  rewrite H' ; omega.
Qed.

Lemma mod_div: forall m:Z, m mod 2 ^ n + 2 ^ n * (m / 2 ^ n) = m.
Proof.
  intro.
  rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq.
  apply pown0.
Qed.

Lemma Zland_pow : forall a b,
  0 <= a < 2 ^ n ->
  Z.land a (2^n * b) = 0.
Proof.
  intros a b Ha.
  apply Z.bits_inj.
  intro m.
  rewrite Z.land_spec ; symmetry.
  assert(Hm: m < n \/ m >= n) by omega.
  rewrite Z.testbit_0_l.
  destruct Hm as [Hm | Hm].
  {
  assert(Z.testbit (2^n * b) m = false).
  rewrite Z.mul_comm; rewrite <- Z.shiftl_mul_pow2.
  apply Z.shiftl_spec_low ; assumption.
  omega.
  rewrite H.
  rewrite Bool.andb_false_r.
  reflexivity.
  }
  assert(Z.testbit a m = false).
  replace (a) with (a mod 2^n).
  apply Z.mod_pow2_bits_high.
  omega.
  apply Zmod_small.
  assumption.
  rewrite H.
  rewrite Bool.andb_false_l.
  reflexivity.
Qed.

Lemma Zxor_add : forall a b,
  0 <= a < 2 ^ n ->
  a + 2^n * b = Z.lxor a (2^n * b).
Proof.
  intros a b Ha.
  apply Z.add_nocarry_lxor.
  apply Zland_pow.
  assumption.
Qed.

Lemma Zor_add : forall a b,
  0 <= a < 2 ^ n ->
  a + 2^n * b = Z.lor a (2^n * b).
Proof.
  intros a b Ha.
  rewrite <- Z.lxor_lor.
  apply Z.add_nocarry_lxor.
  all: apply Zland_pow; assumption.
Qed.

Lemma Z_land_bound : forall a b,
  0 <= a /\ a < 2 ^ n ->
  0 <= b /\ b < 2 ^ n ->
  0 <= Z.land a b /\ Z.land a b < 2 ^ n.
Proof.
  intros a b [Ha Ha'] [Hb Hb'].
  split.
  apply Z.land_nonneg.
  omega.
  assert(Haa: a = 0 \/ 0 < a) by omega.
  destruct Haa as [Haa|Haa].
  subst.
  rewrite Z.land_0_l.
  apply Z.gt_lt.
  apply pown0.
  assert(Hbb: b = 0 \/ 0 < b) by omega.
  destruct Hbb as [Hbb|Hbb].
  subst.
  rewrite Z.land_0_r.
  apply Z.gt_lt.
  apply pown0.
  apply Z.log2_lt_cancel.
  assert(Hab:= Z.log2_land a b Ha Hb).
  assert(Z.min (Z.log2 a) (Z.log2 b) < Z.log2 (2^n)).
  {
  apply Z.log2_lt_pow2 in Ha'.
  2: omega.
  apply Z.log2_lt_pow2 in Hb'.
  2: omega.
  rewrite Z.log2_pow2.
  2: omega.
  apply Z.min_lt_iff.
  omega.
  }
  omega.
Qed.

Lemma Z_lor_bound : forall a b,
  0 <= a /\ a < 2 ^ n ->
  0 <= b /\ b < 2 ^ n ->
  0 <= Z.lor a b /\ Z.lor a b < 2 ^ n.
Proof.
  intros a b [Ha Ha'] [Hb Hb'].
  split.
  apply Z.lor_nonneg.
  omega.
  assert(Haa: a = 0 \/ 0 < a) by omega.
  destruct Haa as [Haa|Haa].
  subst.
  rewrite Z.lor_0_l.
  omega.
  assert(Hbb: b = 0 \/ 0 < b) by omega.
  destruct Hbb as [Hbb|Hbb].
  subst.
  rewrite Z.lor_0_r.
  omega.
  apply Z.log2_lt_cancel.
  assert(Hab:= Z.log2_lor a b Ha Hb).
  assert(Z.max (Z.log2 a) (Z.log2 b) < Z.log2 (2^n)).
  {
  apply Z.log2_lt_pow2 in Ha'.
  2: omega.
  apply Z.log2_lt_pow2 in Hb'.
  2: omega.
  rewrite Z.log2_pow2.
  2: omega.
  apply Z.max_case ; assumption.
  }
  omega.
Qed.

Lemma Z_land_dist : forall a b c,
  Z.land (Z.lxor a b) c = Z.lxor (Z.land a c) (Z.land b c).
Proof.
  intros a b c.
  apply Z.bits_inj.
  intro m.
  rewrite ?Z.lxor_spec.
  rewrite ?Z.land_spec.
  rewrite ?Z.lxor_spec.
  destruct (Z.testbit a m), (Z.testbit b m), (Z.testbit c m); reflexivity.
Qed.

Lemma Z_land_null : forall a b,
  0 <= a < 2^n ->
  Z.land a (2^n * b) = 0.
Proof.
  intros a b c.
  apply Z.bits_inj.
  intro m.
  rewrite Z.land_spec.
  rewrite Z.bits_0.
  assert(Hmn: m < n \/ m >= n) by omega.
  destruct Hmn as [Hmn|Hmn].
  replace (Z.testbit (2 ^ n * b) m) with false.
  apply Bool.andb_false_r.
  symmetry.
  rewrite Z.mul_comm.
  apply Z.mul_pow2_bits_low.
  omega.
  replace a with (a mod 2^n).
  2: apply Z.mod_small ; omega.
  replace (Z.testbit (a mod 2 ^ n) m) with false.
  rewrite Bool.andb_false_l.
  reflexivity.
  symmetry.
  apply Z.mod_pow2_bits_high.
  omega.
Qed.

End Integer.

Close Scope Z.