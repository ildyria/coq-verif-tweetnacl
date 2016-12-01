Require Export Tools.
Require Export notations.
Require Import OpList.
Require Import MinusList.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsubList (a b : list Z) : list Z := match a,b with
| [], q => ZminusList q
| q,[] => q
| h1::q1,h2::q2 => (Z.sub h1 h2) :: ZsubList q1 q2
end.

Notation "A ⊖ B" := (ZsubList A B) (at level 60, right associativity).

Open Scope Z.
Fixpoint ZsubList_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0%nat, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => -h :: (ZsubList_n p [] q)
  | S p, h :: q, []  => h :: (ZsubList_n p q [])
  | S p, h1::q1, h2::q2 => (Z.sub h1 h2) :: (ZsubList_n p q1 q2)
end.

Lemma ZsubList_ZopList_eq: forall  (a b : list Z), ZsubList a b = ZopList Z.sub a b.
Proof.
  induction a ; intros b ; go.
  destruct b ; go.
  destruct b ; go.
  simpl.
  f_equal ; go.
  replace (map (fun x : ℤ => x - 0) a0) with (map (fun x : ℤ => x) a0).
  rewrite map_id ; go.
  apply map_ext ; intros x ; go.
Qed.

Lemma ZsubList_sliced: forall n a b, slice n (a ⊖ b) = ZsubList_n n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; inv Eq ; rewrite <- IHn ; go.
replace (l ⊖ []) with l ; [|induction l] ; go.
Qed.

Lemma ZsubList_nil_r: forall a, a ⊖ [] = a.
Proof. induction a ; go. Qed.

Lemma ZsubList_slice : forall n a b, slice n (a ⊖ b) = (slice n a) ⊖ (slice n b).
Proof. intros n a b ; repeat rewrite ZsubList_ZopList_eq ;  apply ZopList_slice. Qed.

Lemma ZsubList_tail : forall n a b, tail n (a ⊖ b) = (tail n a) ⊖ (tail n b).
Proof. intros n a b ; repeat rewrite ZsubList_ZopList_eq.
rewrite ZopList_tail ; go.
Qed.

Lemma ZsubList_length : forall a b, length (a ⊖ b) = length a \/ length (a ⊖ b) = length b.
Proof.
  intros a b ; repeat rewrite ZsubList_ZopList_eq; apply ZopList_length.
Qed.

Lemma ZsubList_length_max : forall a b, length (a ⊖ b) = max (length a) (length b).
Proof. intros a b ; repeat rewrite ZsubList_ZopList_eq; apply ZopList_length_max. Qed.

