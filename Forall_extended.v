Require Export Tools.
Require Export Forall.

Lemma Forall_slice : forall n A (l:list A) (P:A -> Prop), Forall P l -> Forall P (slice n l).
Proof.
  induction n.
  - intros A [] P H ; go.
  - intros A [] P H ; go.
  simpl.
  rewrite Forall_cons'.
  rewrite Forall_cons' in H.
  destruct H.
  go.
Qed.

Lemma Forall_app : forall A (a b:list A) (P:A -> Prop), Forall P a -> Forall P b -> Forall P (a ++ b).
Proof.
  induction a.
  - intros b P Ha Hb ; go.
  - intros b P Ha Hb ; go.
    simpl.
    rewrite Forall_cons'.
    rewrite Forall_cons' in Ha.
    destruct Ha.
    go.
Qed.

Lemma Forall_tail : forall n A (l:list A) (P:A -> Prop), Forall P l -> Forall P (tail n l).
Proof.
  induction n.
  - intros A [] P H ; go.
  - intros A [] P H ; go.
  simpl.
  rewrite Forall_cons' in H.
  destruct H.
  go.
Qed.