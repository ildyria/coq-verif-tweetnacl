Require Export Coq.ZArith.BinInt.
Require Export List.
Require Export Tools.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZsumList (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (Z.add h1 h2) :: ZsumList q1 q2
end.

Fixpoint ZsumList_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => h :: (ZsumList_n p [] q)
  | S p, h::q, []  => h :: (ZsumList_n p [] q)
  | S p, h1::q1, h2::q2 => (Z.add h1 h2) :: (ZsumList_n p q1 q2)
end.

Lemma ZsumList_empty1: forall h q, ZsumList (h :: q) [] = h :: ZsumList q [].
Proof.
induction q ; go.
Qed.

Lemma ZsumList_empty2: forall h q, ZsumList [] (h :: q) = h :: ZsumList [] q.
Proof.
induction q ; go.
Qed.

Lemma ZsumList_empty3: forall h q, ZsumList (h :: q) [] = h :: ZsumList [] q.
Proof.
induction q ; go.
Qed.

Lemma ZsumList_eq: forall n a b,
  length a <= n ->
  length b <= n ->
    ZsumList a b = ZsumList_n n a b.
Proof.
induction n.
destruct a, b ; go.
intros a b Hla Hlb.
destruct a, b ; go.
rewrite ZsumList_empty2 ; unfold ZsumList_n ; fold ZsumList_n; f_equal ; apply IHn ; go.
simpl in Hla ; apply le_S_n in Hla.
rewrite ZsumList_empty3 ; unfold ZsumList_n ; fold ZsumList_n; f_equal ; apply IHn; go.
simpl in Hla, Hlb ; apply le_S_n in Hla ; apply le_S_n in Hlb.
simpl ; f_equal ; apply IHn ; go.
Qed.

Lemma ZsumList_sliced: forall n a b, slice n (ZsumList a b) = ZsumList_n n a b.
Proof.
induction n ; intros a b ; simpl ; flatten ; try inv Eq ; rewrite <- IHn ; go.
Qed.

Lemma ZsumList_comm: forall a b, ZsumList a b = ZsumList b a.
Proof.
induction a, b ; go.
unfold ZsumList ; fold ZsumList.
rewrite Z.add_comm.
f_equal.
go.
Qed.

Lemma ZsumList_nil_r: forall a, ZsumList a [] = a.
Proof.
induction a; go.
Qed.

Lemma ZsumList_nil_l: forall a, ZsumList [] a = a.
Proof.
go.
Qed.

Lemma ZsumList_assoc : forall a b c, ZsumList (ZsumList a b) c = ZsumList a (ZsumList b c).
Proof.
induction a, b; go.
intro c.
simpl.
flatten.
rewrite Zplus_assoc_reverse.
f_equal.
apply IHa.
Qed.

Lemma ZsumList_slice : forall n a b, slice n (ZsumList a b) = ZsumList (slice n a) (slice n b).
Proof.
induction n ; intros a b ; destruct a; destruct b ; go.
Qed.

Lemma ZsumList_tail : forall n a b, tail n (ZsumList a b) = ZsumList (tail n a) (tail n b).
Proof.
induction n ; intros a b ; destruct a; destruct b ; go.
simpl; rewrite ZsumList_nil_r; go.
Qed.

Lemma ZsumList_length : forall a b, length (ZsumList a b) = length a \/ length (ZsumList a b) = length b.
Proof.
induction a.
destruct b.
left ; go.
right ; go.
intro b.
destruct b.
go.
simpl.
assert(fklemma: forall x y, S x = S y <-> x = y) by go.
rewrite! fklemma.
go.
Qed.

Lemma ZsumList_length_max : forall a b, length (ZsumList a b) = max (length a) (length b).
Proof.
induction a; destruct b ; go.
Qed.

