Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import stdpp.prelude.
Import ListNotations.


Open Scope Z.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsumList (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (Z.add h1 h2) :: ZsumList q1 q2
end.

Notation "A ⊕ B" := (ZsumList A B) (at level 60, right associativity).

Fixpoint ZsumList_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0%nat, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => h :: (ZsumList_n p [] q)
  | S p, h::q, []  => h :: (ZsumList_n p [] q)
  | S p, h1::q1, h2::q2 => (Z.add h1 h2) :: (ZsumList_n p q1 q2)
end.

Lemma ZsumList_Zipp_eq: forall  (a b : list Z), ZsumList a b = Zipp Z.add a b.
Proof.
  induction a ; destruct b ; go.
  rewrite Zipp_nil_l ; go.
  rewrite Zipp_nil_r ; go.
  intro x ; go.
Qed.

Lemma ZsumList_n_taked: forall n a b, take n (a ⊕ b) = ZsumList_n n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; try rewrite <- IHn ; go. Qed.

Lemma ZsumList_n_Zipp_n_eq: forall n (a b : list Z), ZsumList_n n a b = Zipp_n Z.add n a b.
Proof.
  induction n.
  intros ; go.
  destruct a, b; go;
  rewrite <- ZsumList_n_taked ; rewrite <- Zipp_taked.
  rewrite Zipp_nil_l ; go.
  rewrite Zipp_nil_r ; go.
  intro x ; go.
Qed.

Lemma ZsumList_n_length : forall (n:nat) (a b : list Z), length (ZsumList_n n a b) = min n (max (length a) (length b)).
Proof. intros; repeat rewrite ZsumList_Zipp_eq; rewrite ZsumList_n_Zipp_n_eq ;  apply Zipp_n_length.
Qed.

Lemma ZsumList_n_Zlength : forall (n:nat) (a b : list Z), Zlength (ZsumList_n n a b) = Zmin n (Zmax (Zlength a) (Zlength b)).
Proof. intros; repeat rewrite ZsumList_Zipp_eq; rewrite ZsumList_n_Zipp_n_eq ; apply Zipp_n_Zlength. Qed.

Lemma ZsumList_n_nth_length : forall (n : nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  ZsumList_n (S n) a b = (ZsumList_n n a b) ++ [(nth n a 0) + (nth n b 0)].
Proof. intros; repeat rewrite ZsumList_n_Zipp_n_eq. apply Zipp_n_nth_length ; auto. Qed.

Lemma ZsumList_n_nth_Zlength : forall (n : nat) (a b : list Z),
  Zlength a = Zlength b ->
  n < Zlength a ->
  ZsumList_n (S n) a b = (ZsumList_n n a b) ++ [(nth n a 0) + (nth n b 0)].
Proof. convert_length_to_Zlength ZsumList_n_nth_length. Qed.

Lemma ZsumList_comm: forall a b, a ⊕ b = b ⊕ a.
Proof.
  intros a b.
  repeat rewrite ZsumList_Zipp_eq.
  apply Zipp_comm.
  intros x y ; omega.
Qed.

Lemma ZsumList_nil_r: forall a, a ⊕ [] = a.
Proof.
  intros a.
  rewrite ZsumList_Zipp_eq.
  apply Zipp_nil_r.
  intros x ; omega.
Qed.

Lemma ZsumList_nil_l: forall a, [] ⊕ a = a.
Proof. go. Qed.

Lemma ZsumList_assoc : forall a b c, (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c).
Proof.
  intros a b c.
  repeat rewrite ZsumList_Zipp_eq.
  apply Zipp_assoc.
  intros x y z ; omega.
  intros x ; omega.
  intros x ; omega.
Qed.

Lemma ZsumList_take : forall n a b, take n (a ⊕ b) = (take n a) ⊕ (take n b).
Proof. intros n a b ; repeat rewrite ZsumList_Zipp_eq ;  apply Zipp_take. Qed.

Lemma ZsumList_drop : forall n a b, drop n (a ⊕ b) = (drop n a) ⊕ (drop n b).
Proof. intros n a b ; repeat rewrite ZsumList_Zipp_eq ;  apply Zipp_drop ; go. Qed.

Lemma ZsumList_length : forall a b, length (a ⊕ b) = length a \/ length (a ⊕ b) = length b.
Proof. intros a b ; repeat rewrite ZsumList_Zipp_eq; apply Zipp_length. Qed.

Lemma ZsumList_Zlength : forall a b, Zlength (a ⊕ b) = Zlength a \/ Zlength (a ⊕ b) = Zlength b.
Proof. intros a b ; repeat rewrite ZsumList_Zipp_eq; apply Zipp_Zlength. Qed.

Lemma ZsumList_length_max : forall a b, length (a ⊕ b) = max (length a) (length b).
Proof. intros a b ; repeat rewrite ZsumList_Zipp_eq; apply Zipp_length_max. Qed.

Lemma ZsumList_Zlength_max : forall a b, Zlength (a ⊕ b) = Zmax (Zlength a) (Zlength b).
Proof. intros a b ; repeat rewrite ZsumList_Zipp_eq; apply Zipp_Zlength_max. Qed.

Close Scope Z.