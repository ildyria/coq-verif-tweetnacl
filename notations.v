Require Export Coq.ZArith.BinInt.
Require Export Coq.ZArith.Zdiv.
Require Export Coq.Lists.List.

Open Scope Z.

Notation "ℤ.ℕ A" := (Z.of_nat A) (at level 60, right associativity).
Notation "A :𝓟" := (A mod (2^255 - 19)) (at level 80, right associativity).

Close Scope Z.
