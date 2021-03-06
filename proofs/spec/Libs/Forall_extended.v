Require Import stdpp.list.
From Tweetnacl Require Export Libs.Lists_extended.
From Tweetnacl Require Import Libs.LibTactics.

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
  intros P d Hnth ; apply Forall_cons_2.
  apply (Hnth 0).
  eapply IHl.
  intros i.
  apply (Hnth (S i)).
Qed.

Lemma upd_nth_Forall: forall i A (l:list A) (P: A -> Prop) v,
  Forall P l -> P v ->
  Forall P (upd_nth i l v).
Proof.
  induction i => A [|h q] P v Hl Hv ; simpl;
  try solve[apply Forall_cons_2 ; go];
  apply Forall_cons in Hl ; destruct Hl as [Ha Hl] ; apply Forall_cons_2 ; go.
Qed.

Lemma Forall_take_n_m : forall m n A (l:list A) (P: A -> Prop),
  n <= m ->
  Forall P (take m l) -> Forall P (take n l).
Proof.
induction m ; intros.
inv H.
rewrite firstn_O ; apply Forall_nil_2.
destruct n.
rewrite firstn_O ; apply Forall_nil_2.
destruct l.
simpl ; apply Forall_nil_2.
simpl.
simpl in H0.
apply Forall_cons in H0 ; destruct H0.
apply Forall_cons_2 ; go.
Qed.

Open Scope Z.

Lemma Forall_bounds_le_lt: forall a b l,
  Forall (fun x => a < x < b) l ->
    Forall (fun x => a <= x <= b) l.
Proof. intros; eapply Forall_impl ; eauto ; intros ; go. Qed.

Close Scope Z.