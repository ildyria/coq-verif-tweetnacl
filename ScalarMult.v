Require Export ZofList.
Import ListNotations.
Require Import Tools.

Open Scope Z.

Fixpoint ZscalarMult (a:Z) (b:list Z) : list Z := match b with
| [] => []
| h :: q => a * h :: ZscalarMult a q
end.

Notation "A ∘ B" := (ZscalarMult A B) (at level 60, right associativity).

Lemma ZscalarMultnil : forall n, n ∘ [] = [].
Proof. go. Qed.

Lemma ZscalarMult_length: forall n l, length (n ∘ l) = length l.
Proof. intro n ; induction l ; go. Qed.

Lemma ZscalarMult_slice: forall l n m, slice n (m ∘ l) = m ∘ (slice n l).
Proof. induction l ; intros [] m; go. Qed.

Lemma ZscalarMult_tail: forall l n m, tail n (m ∘ l) = m ∘ (tail n l).
Proof. induction l ; intros [] m; go. Qed.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZscalarMult_correct: forall a b, ℤ.lst a ∘ b = a * ℤ.lst b.
Proof.
  intros a ; induction b ; go.
  unfold ZscalarMult ; fold ZscalarMult.
  rewrite! ZofList_cons.
  rewrite IHb.
  ring.
Qed.

End Integer.

Close Scope Z.
