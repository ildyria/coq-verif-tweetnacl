Require Export Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z.

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
  Zmin (Zmin (min1*min2) (max1*max2)) (Zmin (max1*min2) (min1*max2)).

Definition max_prod (min1 max1 min2 max2: Z) : Z:=
  Zmax (Zmax (min1*min2) (max1*max2)) (Zmax (max1*min2) (min1*max2)).

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

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma pown: 2 ^ n > 1.
Proof. rewrite Z.gt_lt_iff ; apply Z.pow_gt_1 ; omega. Qed.

Lemma pown0: 2 ^ n > 0.
Proof. assert(Hp:= pown) ; omega. Qed.

Lemma pown2: 2 <= 2 ^ n.
Proof. change 2 with (2 ^ 1) ;apply Z.pow_le_mono ; change (2^1) with 2 ; omega. Qed.

End Integer.

Close Scope Z.