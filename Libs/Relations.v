Require Export Coq.ZArith.ZArith.

Open Scope Z.

Module bounds.

Lemma lt_lt_trans: forall (b c a d x:Z),
  b < x < c ->
  a <= b ->
  c <= d ->
  a < x < d.
Proof. intros b c a d x [] ; split ; omega. Qed.

Lemma lt_impl_le: forall (a b x:Z),
  a < x < b ->
  a <= x <= b.
Proof. intros ; split ; omega. Qed.

Lemma le_le_trans: forall (a b c d x:Z),
  b <= x <= c ->
  a <= b ->
  c <= d ->
  a <= x <= d.
Proof. intros a b c d x [] ; split ; omega. Qed.

Lemma le_lt_trans: forall (b c a d x:Z),
  b <= x <= c ->
  a < b ->
  c < d ->
  a < x < d.
Proof. intros b c a d x [] ; split ; omega. Qed.

End bounds.

Close Scope Z.

