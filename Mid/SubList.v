Require Import stdpp.prelude.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.MinusList.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsubList (a b : list Z) : list Z := match a,b with
| [], q => ZminusList q
| q,[] => q
| h1::q1,h2::q2 => (Z.sub h1 h2) :: ZsubList q1 q2
end.

Notation "A ⊖ B" := (ZsubList A B) (at level 60, right associativity).

Open Scope Z.

Lemma ZsubList_Zipp_eq: forall  (a b : list Z), ZsubList a b = Zipp Z.sub a b.
Proof. elim=> [|h a IHa]. move=> [|b h]; go.
       move => [|b lb] ; simpl.
  f_equal ; go.
  replace (map (fun x : ℤ => x - 0) a) with (map (fun x : ℤ => x) a).
  rewrite map_id ; go.
  apply map_ext ; intros x ; go.
  f_equal ; go.
Qed.

Lemma ZsubList_nth : forall (n:nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  nth n (a ⊖ b) 0 = (nth n a 0) - (nth n b 0).
Proof. intros; rewrite ?ZsubList_Zipp_eq; apply Zipp_nth_length ; auto. Qed.

Lemma ZsubList_nth_Zlength : forall (n:Z) (a b : list Z),
  0 <= n ->
  Zlength a = Zlength b ->
  n < Zlength a ->
  nth (Z.to_nat n) (a ⊖ b) 0 = (nth (Z.to_nat n) a 0) - (nth (Z.to_nat n) b 0).
Proof. intros; rewrite ?ZsubList_Zipp_eq; apply Zipp_nth_Zlength ; auto. Qed.

Lemma ZsubList_nil_r: forall a, a ⊖ [] = a.
Proof. elim ; go. Qed.

Lemma ZsubList_take : forall n a b, take n (a ⊖ b) = (take n a) ⊖ (take n b).
Proof. intros n a b ; rewrite ?ZsubList_Zipp_eq ;  apply Zipp_take. Qed.

Lemma ZsubList_drop : forall n a b, drop n (a ⊖ b) = (drop n a) ⊖ (drop n b).
Proof. intros n a b ; rewrite ?ZsubList_Zipp_eq.
rewrite Zipp_drop ; go.
Qed.

Lemma ZsubList_length : forall a b, length (a ⊖ b) = length a \/ length (a ⊖ b) = length b.
Proof.
  intros a b ; rewrite ?ZsubList_Zipp_eq; apply Zipp_length.
Qed.

Lemma ZsubList_Zlength : forall a b, Zlength (a ⊖ b) = Zlength a \/ Zlength (a ⊖ b) = Zlength b.
Proof.
  intros a b ; rewrite ?ZsubList_Zipp_eq; apply Zipp_Zlength.
Qed.

Lemma ZsubList_length_max : forall a b, length (a ⊖ b) = max (length a) (length b).
Proof. intros a b ; rewrite ?ZsubList_Zipp_eq; apply Zipp_length_max. Qed.

Lemma ZsubList_Zlength_max : forall a b, Zlength (a ⊖ b) = Zmax (Zlength a) (Zlength b).
Proof. intros a b ; rewrite ?ZsubList_Zipp_eq; apply Zipp_Zlength_max. Qed.

Close Scope Z.