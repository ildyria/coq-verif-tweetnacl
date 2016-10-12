Require Export Coq.ZArith.BinInt.
Require Export List.
Require Export Tools.
Import ListNotations.
Require Export ToFF.

Fixpoint ZscalarMult a b := match b with
| [] => []
| h :: q => a * h :: ZscalarMult a q
end.

Lemma ZscalarMultToFF: forall n a b, ToFF n (ZscalarMult a b) = a * ToFF n b.
Proof.
intros n a.
induction b ; go.
unfold ZscalarMult ; fold ZscalarMult.
rewrite! ToFF_cons.
rewrite IHb.
ring.
Qed.

Lemma ZscalarMultnil : forall n, ZscalarMult n [] = [].
Proof.
go.
Qed.

Lemma ZscalarMult_length: forall n l, length (ZscalarMult n l) = length l.
Proof.
intro n ; induction l ; go.
Qed.

Lemma ZscalarMult_slice: forall l n m, slice n (ZscalarMult m l) = ZscalarMult m (slice n l).
Proof.
induction l ; intros [] m; go.
Qed.

Lemma ZscalarMult_tail: forall l n m, tail n (ZscalarMult m l) = ZscalarMult m (tail n l).
Proof.
induction l ; intros [] m; go.
Qed.

