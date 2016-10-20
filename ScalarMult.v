Require Export Coq.ZArith.BinInt.
Require Export List.
Require Export Tools.
Import ListNotations.
Require Export ToFF.

Fixpoint ZscalarMult (a:Z) (b:list Z) : list Z := match b with
| [] => []
| h :: q => a * h :: ZscalarMult a q
end.

Notation "A ∘ B" := (ZscalarMult A B) (at level 60, right associativity).

Lemma ZscalarMultToFF: forall n a b, ToFF n (a ∘ b) = a * ToFF n b.
Proof.
intros n a.
induction b ; go.
unfold ZscalarMult ; fold ZscalarMult.
rewrite! ToFF_cons.
rewrite IHb.
ring.
Qed.

Lemma ZscalarMultnil : forall n, n ∘ [] = [].
Proof.
go.
Qed.

Lemma ZscalarMult_length: forall n l, length (n ∘ l) = length l.
Proof.
intro n ; induction l ; go.
Qed.

Lemma ZscalarMult_slice: forall l n m, slice n (m ∘ l) = m ∘ (slice n l).
Proof.
induction l ; intros [] m; go.
Qed.

Lemma ZscalarMult_tail: forall l n m, tail n (m ∘ l) = m ∘ (tail n l).
Proof.
induction l ; intros [] m; go.
Qed.

