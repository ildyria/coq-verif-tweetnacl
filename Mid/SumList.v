Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.

Open Scope Z.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsumList (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (Z.add h1 h2) :: ZsumList q1 q2
end.

Notation "A ⊕ B" := (ZsumList A B) (at level 60, right associativity).

Lemma ZsumList_Zipp_eq: forall  (a b : list Z), ZsumList a b = Zipp Z.add a b.
Proof.
  elim => [|a l IHa] [|b Hb] ; go.
  rewrite Zipp_nil_l ; go.
  rewrite Zipp_nil_r ; go.
  intro x ; go.
Qed.

Lemma ZsumList_nth : forall (n:nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  nth n (a ⊕ b) 0 = (nth n a 0) + (nth n b 0).
Proof. intros; rewrite ?ZsumList_Zipp_eq; apply Zipp_nth_length ; auto. Qed.

Lemma ZsumList_comm: forall a b, a ⊕ b = b ⊕ a.
Proof.
  move => a b.
  rewrite ?ZsumList_Zipp_eq.
  apply Zipp_comm => x y ; omega.
Qed.

Lemma ZsumList_nil_r: forall a, a ⊕ [] = a.
Proof.
  intros a.
  rewrite ZsumList_Zipp_eq.
  apply Zipp_nil_r => x ; omega.
Qed.

Lemma ZsumList_nil_l: forall a, [] ⊕ a = a.
Proof. go. Qed.

Lemma ZsumList_assoc : forall a b c, (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c).
Proof.
  move=> a b c.
  rewrite ?ZsumList_Zipp_eq.
  apply Zipp_assoc => x ; try omega.
  move=> y z ; omega.
Qed.

Lemma ZsumList_take : forall n a b, take n (a ⊕ b) = (take n a) ⊕ (take n b).
Proof. intros n a b ; rewrite ?ZsumList_Zipp_eq ;  apply Zipp_take. Qed.

Lemma ZsumList_drop : forall n a b, drop n (a ⊕ b) = (drop n a) ⊕ (drop n b).
Proof. intros n a b ; rewrite ?ZsumList_Zipp_eq ;  apply Zipp_drop ; go. Qed.

Lemma ZsumList_length : forall a b, length (a ⊕ b) = length a \/ length (a ⊕ b) = length b.
Proof. intros a b ; rewrite ?ZsumList_Zipp_eq; apply Zipp_length. Qed.

Lemma ZsumList_Zlength : forall a b, Zlength (a ⊕ b) = Zlength a \/ Zlength (a ⊕ b) = Zlength b.
Proof. intros a b ; rewrite ?ZsumList_Zipp_eq; apply Zipp_Zlength. Qed.

Lemma ZsumList_length_max : forall a b, length (a ⊕ b) = max (length a) (length b).
Proof. intros a b ; rewrite ?ZsumList_Zipp_eq; apply Zipp_length_max. Qed.

Lemma ZsumList_Zlength_max : forall a b, Zlength (a ⊕ b) = Zmax (Zlength a) (Zlength b).
Proof. intros a b ; rewrite ?ZsumList_Zipp_eq; apply Zipp_Zlength_max. Qed.

Close Scope Z.