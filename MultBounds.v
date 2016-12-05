Require Import Tools.
Require Import Psatz.

Open Scope Z.
Lemma Mult_interval_correct_min_max :
  forall a b c d x y : Z,
    a < x < b ->
    c < y < d ->
    Zmin (Zmin (a*c) (b*d)) (Zmin (b*c) (a*d)) < x * y
        < Zmax (Zmax (a*c) (b*d)) (Zmax (b*c) (a*d)).
Proof.
  intros. split.
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
