Require Export SumList.
Require Export ToFF.
Import ListNotations.

Open Scope Z.

Lemma ZsumListToFF : forall n a b o, a ⊕ b = o -> ToFF n a + ToFF n b = ToFF n o.
Proof.
intro n ; induction a , b.
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
  unfold ToFF.
  unfold ToFF.ToFF.
  rewrite <- Z.add_shuffle2.
  rewrite Zred_factor4.
  apply Zplus_eq_compat.
  apply Hh.
  f_equal.
  rewrite Z.add_comm.
  apply HSum.
Qed.

Corollary ZsumListToFF2: forall n a b, ToFF n (a ⊕ b) = ToFF n a + ToFF n b.
Proof.
intros n a b.
assert(exists o, o = a ⊕ b) by (exists (a ⊕ b) ; go) ; destruct H.
symmetry; subst x ; apply ZsumListToFF ; go.
Qed.
