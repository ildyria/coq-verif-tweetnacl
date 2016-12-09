Require Import Tools.
Require Import Psatz.

Open Scope Z.

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

Close Scope Z.