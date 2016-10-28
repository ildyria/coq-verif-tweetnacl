Require Export SumList.
Require Export ZofList.
Import ListNotations.

Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZsumList_correct_impl : forall a b o, a ⊕ b = o -> (ℤ.lst a) + (ℤ.lst b) = ℤ.lst o.
Proof.
induction a , b.
- intros o HSum ; go.
- intros o HSum ; go.
- intros o HSum ; go.
- intros o HSum.
  destruct o ; go.
  simpl in HSum.
  assert(Hh:= HSum).
  apply headSame in Hh.
  apply tailSame in HSum.
  apply IHa in HSum.
  unfold ZofList.
  rewrite <- Z.add_shuffle2.
  rewrite Zred_factor4.
  apply Zplus_eq_compat.
  apply Hh.
  f_equal.
  rewrite Z.add_comm.
  apply HSum.
Qed.

Corollary ZsumList_correct: forall a b, (ℤ.lst a ⊕ b) = (ℤ.lst a) + (ℤ.lst b).
Proof.
intros a b.
assert(exists o, o = a ⊕ b) by (exists (a ⊕ b) ; go) ; destruct H.
symmetry; subst x ; apply ZsumList_correct_impl ; go.
Qed.

End Integer.
