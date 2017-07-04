Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.

Require Import Tweetnacl.Op.MinusList.
Require Import stdpp.prelude.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsubList (a b : list Z) : list Z := match a,b with
| [], q => ZminusList q
| q,[] => q
| h1::q1,h2::q2 => (Z.sub h1 h2) :: ZsubList q1 q2
end.

Notation "A ⊖ B" := (ZsubList A B) (at level 60, right associativity).

Open Scope Z.
(*
Fixpoint ZsubList_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0%nat, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => -h :: (ZsubList_n p [] q)
  | S p, h :: q, []  => h :: (ZsubList_n p q [])
  | S p, h1::q1, h2::q2 => (Z.sub h1 h2) :: (ZsubList_n p q1 q2)
end.
*)
Lemma ZsubList_Zipp_eq: forall  (a b : list Z), ZsubList a b = Zipp Z.sub a b.
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
(*
Lemma ZsubList_taked: forall n a b, take n (a ⊖ b) = ZsubList_n n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; try rewrite <- IHn ; go.
replace (l ⊖ []) with l ; [|induction l] ; go.
Qed.
*)

Lemma ZsubList_nth : forall (n:nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  nth n (a ⊖ b) 0 = (nth n a 0) - (nth n b 0).
Proof. intros; repeat rewrite ZsubList_Zipp_eq; apply Zipp_nth_length ; auto. Qed.

Lemma ZsubList_nil_r: forall a, a ⊖ [] = a.
Proof. induction a ; go. Qed.

Lemma ZsubList_take : forall n a b, take n (a ⊖ b) = (take n a) ⊖ (take n b).
Proof. intros n a b ; repeat rewrite ZsubList_Zipp_eq ;  apply Zipp_take. Qed.

Lemma ZsubList_drop : forall n a b, drop n (a ⊖ b) = (drop n a) ⊖ (drop n b).
Proof. intros n a b ; repeat rewrite ZsubList_Zipp_eq.
rewrite Zipp_drop ; go.
Qed.

Lemma ZsubList_length : forall a b, length (a ⊖ b) = length a \/ length (a ⊖ b) = length b.
Proof.
  intros a b ; repeat rewrite ZsubList_Zipp_eq; apply Zipp_length.
Qed.

Lemma ZsubList_Zlength : forall a b, Zlength (a ⊖ b) = Zlength a \/ Zlength (a ⊖ b) = Zlength b.
Proof.
  intros a b ; repeat rewrite ZsubList_Zipp_eq; apply Zipp_Zlength.
Qed.

Lemma ZsubList_length_max : forall a b, length (a ⊖ b) = max (length a) (length b).
Proof. intros a b ; repeat rewrite ZsubList_Zipp_eq; apply Zipp_length_max. Qed.

Lemma ZsubList_Zlength_max : forall a b, Zlength (a ⊖ b) = Zmax (Zlength a) (Zlength b).
Proof. intros a b ; repeat rewrite ZsubList_Zipp_eq; apply Zipp_Zlength_max. Qed.
(*
Lemma ZsubList_n_taked: forall n a b, take n (a ⊖ b) = ZsubList_n n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; try rewrite <- IHn ; try rewrite! ZsubList_nil_r ;  go. Qed.

Lemma ZsubList_n_Zipp_n_eq: forall n (a b : list Z), ZsubList_n n a b = Zipp_n Z.sub n a b.
Proof.
  induction n.
  intros ; go.
  destruct a, b; go;
  rewrite <- ZsubList_n_taked ; rewrite <- Zipp_taked.
  rewrite Zipp_nil_r ; go.
  intro x ; go.
Qed.

Lemma ZsubList_n_length : forall (n:nat) (a b : list Z), length (ZsubList_n n a b) = min n (max (length a) (length b)).
Proof. intros; repeat rewrite ZsumList_Zipp_eq; rewrite ZsubList_n_Zipp_n_eq ;  apply Zipp_n_length. Qed.

Lemma ZsubList_n_Zlength : forall (n:nat) (a b : list Z), Zlength (ZsubList_n n a b) = Zmin n (Zmax (Zlength a) (Zlength b)).
Proof. intros; repeat rewrite ZsubList_Zipp_eq; rewrite ZsubList_n_Zipp_n_eq ; apply Zipp_n_Zlength. Qed.

Lemma ZsubList_n_nth_length : forall (n : nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  ZsubList_n (S n) a b = (ZsubList_n n a b) ++ [(nth n a 0) - (nth n b 0)].
Proof. intros; repeat rewrite ZsubList_n_Zipp_n_eq. apply Zipp_n_nth_length ; auto. Qed.

Lemma ZsubList_n_nth_Zlength : forall (n : nat) (a b : list Z),
  Zlength a = Zlength b ->
  n < Zlength a ->
  ZsubList_n (S n) a b = (ZsubList_n n a b) ++ [(nth n a 0) - (nth n b 0)].
Proof. convert_length_to_Zlength ZsubList_n_nth_length. Qed.
*)

Close Scope Z.