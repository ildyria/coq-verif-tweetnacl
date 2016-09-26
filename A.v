Require Export SumList.
Require Export ToFF.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Import ListNotations.

Open Scope Z.

Lemma sumListToFF : forall n a b o, sum_list_Z a b = o -> ToFF n a + ToFF n b = ToFF n o.
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

Corollary sumListToFF2: forall n a b, ToFF n (sum_list_Z a b) = ToFF n a + ToFF n b.
Proof.
intros n a b.
assert(exists o, o = sum_list_Z a b) by (exists (sum_list_Z a b) ; go) ; destruct H.
symmetry; subst x ; apply sumListToFF ; go.
Qed.