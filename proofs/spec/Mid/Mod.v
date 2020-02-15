Require Import ZArith.

Local Open Scope Z.
Definition modP x := Z.modulo x (Z.pow 2 255 - 19).
