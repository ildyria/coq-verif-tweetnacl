Require Export Tools.
Require Export notations.
Require Export ZbinopList.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsumList (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (Z.add h1 h2) :: ZsumList q1 q2
end.

Notation "A ⊕ B" := (ZsumList A B) (at level 60, right associativity).

Fixpoint ZsumList_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => h :: (ZsumList_n p [] q)
  | S p, h::q, []  => h :: (ZsumList_n p [] q)
  | S p, h1::q1, h2::q2 => (Z.add h1 h2) :: (ZsumList_n p q1 q2)
end.

Lemma ZsumList_ZbinopList_eq: forall  (a b : list Z), ZsumList a b = ZbinopList Z.add a b.
Proof.
  induction a ; intros b ; go.
  destruct b ; go.
  rewrite ZbinopList_nil_l ; go.
  destruct b ; go.
  rewrite ZbinopList_nil_r ; go.
  intro x ; go.
Qed.

Lemma ZsumList_sliced: forall n a b, slice n (a ⊕ b) = ZsumList_n n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; try inv Eq ; rewrite <- IHn ; go. Qed.

Lemma ZsumList_comm: forall a b, a ⊕ b = b ⊕ a.
Proof.
  intros a b.
  repeat rewrite ZsumList_ZbinopList_eq.
  apply ZbinopList_comm.
  go.
  intros x y ; omega.
Qed.

Lemma ZsumList_nil_r: forall a, a ⊕ [] = a.
Proof.
  intros a.
  rewrite ZsumList_ZbinopList_eq.
  apply ZbinopList_nil_r.
  go.
  intros x ; omega.
Qed.

Lemma ZsumList_nil_l: forall a, [] ⊕ a = a.
Proof. go. Qed.

Lemma ZsumList_assoc : forall a b c, (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c).
Proof.
  intros a b c.
  repeat rewrite ZsumList_ZbinopList_eq.
  apply ZbinopList_assoc.
  go.
  intros x y z ; omega.
  intros x ; omega.
  intros x ; omega.
Qed.

Lemma ZsumList_slice : forall n a b, slice n (a ⊕ b) = (slice n a) ⊕ (slice n b).
Proof. intros n a b ; repeat rewrite ZsumList_ZbinopList_eq ;  apply ZbinopList_slice. Qed.

Lemma ZsumList_tail : forall n a b, tail n (a ⊕ b) = (tail n a) ⊕ (tail n b).
Proof. intros n a b ; repeat rewrite ZsumList_ZbinopList_eq ;  apply ZbinopList_tail ; go.
Qed.

Lemma ZsumList_length : forall a b, length (a ⊕ b) = length a \/ length (a ⊕ b) = length b.
Proof.
  intros a b ; repeat rewrite ZsumList_ZbinopList_eq; apply ZbinopList_length.
Qed.

Lemma ZsumList_length_max : forall a b, length (a ⊕ b) = max (length a) (length b).
Proof. intros a b ; repeat rewrite ZsumList_ZbinopList_eq; apply ZbinopList_length_max. Qed.

