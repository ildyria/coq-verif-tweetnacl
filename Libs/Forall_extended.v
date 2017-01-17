Require Export Libs.Lists_extended.
Require Export Libs.Forall.

Lemma Forall_slice: forall n A (l:list A) (P:A -> Prop),
  Forall P l -> 
    Forall P (slice n l).
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

Lemma Forall_app: forall A (a b:list A) (P:A -> Prop),
  Forall P a ->
  Forall P b ->
    Forall P (a ++ b).
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

Lemma Forall_app_inv : forall A (a b:list A) (P:A -> Prop),
  Forall P (a ++ b) -> Forall P a /\ Forall P b.
Proof.
  induction a.
  - intros b P H ; go.
  - intros b P H ; go.
    rewrite consApp2 in H.
    rewrite Forall_cons' in H.
    destruct H as [Ha Hc].
    apply IHa in Hc.
    destruct Hc as [Ha0 Hb].
    rewrite Forall_cons'.
    go.
Qed.

Lemma Forall_tail: forall n A (l:list A) (P:A -> Prop),
  Forall P l ->
    Forall P (tail n l).
Proof.
  induction n.
  - intros A [] P H ; go.
  - intros A [] P H ; go.
  simpl.
  rewrite Forall_cons' in H.
  destruct H.
  go.
Qed.

Lemma Forall_nth_d: forall A (l:list A) (P:A -> Prop) d,
  P d ->
  Forall P l ->
    forall i, P (nth i l d).
Proof.
  intros A l P d Hd Hl.
  induction l ; destruct i ; inv Hl ; go.
Qed.

Lemma Forall_nth_len: forall A (l:list A) (P:A -> Prop) d,
  Forall P l ->
    forall i, i < length l -> 
      P (nth i l d).
Proof.
  intros A l P d Hl.
  induction l; intros i Hi.
  - simpl in Hi.
    inv Hi.
  - destruct i; inv Hl ; go.
Qed.

Lemma nth_Forall: forall A (l: list A) (P:A -> Prop) d,
  (forall i, P (nth i l d)) ->
    Forall P l.
Proof.
  induction l ; go.
  intros P d Hnth ; rewrite Forall_cons'.
  split.
  apply (Hnth 0).
  eapply IHl.
  intros i.
  apply (Hnth (S i)).
Qed.
