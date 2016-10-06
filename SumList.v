Require Export Coq.ZArith.BinInt.
Require Export Tools.
Require Export List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint sum_list_Z (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (Z.add h1 h2) :: sum_list_Z q1 q2
end.

Fixpoint sum_list_Z_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => h :: (sum_list_Z_n p [] q)
  | S p, h::q, []  => h :: (sum_list_Z_n p [] q)
  | S p, h1::q1, h2::q2 => (Z.add h1 h2) :: (sum_list_Z_n p q1 q2)
end.

Lemma sum_list_Z_empty1: forall h q, sum_list_Z (h :: q) [] = h :: sum_list_Z q [].
Proof.
induction q ; go.
Qed.

Lemma sum_list_Z_empty2: forall h q, sum_list_Z [] (h :: q) = h :: sum_list_Z [] q.
Proof.
induction q ; go.
Qed.

Lemma sum_list_Z_empty3: forall h q, sum_list_Z (h :: q) [] = h :: sum_list_Z [] q.
Proof.
induction q ; go.
Qed.

Lemma sum_list_eq: forall n a b,
  length a <= n ->
  length b <= n ->
    sum_list_Z a b = sum_list_Z_n n a b.
Proof.
induction n.
destruct a, b ; go.
intros a b Hla Hlb.
destruct a, b ; go.
rewrite sum_list_Z_empty2 ; unfold sum_list_Z_n ; fold sum_list_Z_n; f_equal ; apply IHn ; go.
simpl in Hla ; apply le_S_n in Hla.
rewrite sum_list_Z_empty3 ; unfold sum_list_Z_n ; fold sum_list_Z_n; f_equal ; apply IHn; go.
simpl in Hla, Hlb ; apply le_S_n in Hla ; apply le_S_n in Hlb.
simpl ; f_equal ; apply IHn ; go.
Qed.

Lemma sum_sliced: forall n a b, slice n (sum_list_Z a b) = sum_list_Z_n n a b.
Proof.
induction n ; intros a b ; simpl ; flatten ; try inv Eq ; rewrite <- IHn ; go.
Qed.

Lemma sum_list_comm: forall a b, sum_list_Z a b = sum_list_Z b a.
Proof.
induction a, b ; go.
unfold sum_list_Z ; fold sum_list_Z.
rewrite Z.add_comm.
f_equal.
go.
Qed.

Lemma sum_list_nil_r: forall a, sum_list_Z a [] = a.
Proof.
induction a; go.
Qed.

Lemma sum_list_nil_l: forall a, sum_list_Z [] a = a.
Proof.
go.
Qed.

Lemma sum_list_assoc : forall a b c, sum_list_Z (sum_list_Z a b) c = sum_list_Z a (sum_list_Z b c).
Proof.
induction a, b; go.
intro c.
simpl.
flatten.
rewrite Zplus_assoc_reverse.
f_equal.
apply IHa.
Qed.
