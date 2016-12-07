Require Export Coq.ZArith.BinInt.
Require Export Coq.ZArith.Zdiv.

Open Scope Z.

Notation "ℤ.ℕ A" := (Z.of_nat A) (at level 60, right associativity).
Notation "A :𝓖𝓕" := (A mod (2^255 - 19)) (at level 40, left associativity).
(*Print Grammar pattern.*)
Notation ℕ := nat.
Notation ℤ := Z.

Close Scope Z.
