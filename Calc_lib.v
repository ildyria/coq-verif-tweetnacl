Require Export Coq.ZArith.ZArith.
Require Import Psatz.

Open Scope Z.

SearchAbout Z.mul.
Lemma Zred_factor6 : forall m n, (1 + m) * n = n + n * m.
Proof. intros ; Psatz.nia. Qed.

Lemma Zred_factor7 : forall m n, (1 + m) * n = n + m * n.
Proof. intros ; Psatz.nia. Qed.

Lemma Zred_factor8: forall n m p : Z, m * n + p * n = (m + p) * n.
Proof. intros ; Psatz.nia. Qed.

Close Scope Z.