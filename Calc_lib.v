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

Close Scope Z.