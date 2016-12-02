Require Export Tools.
Require Export notations.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZunopList (f:Z -> Z -> Z) (a:Z) (b : list Z) : list Z := match b with
  | [] => []
  | h :: q => f a h :: ZunopList f a q
end.

Fixpoint ZunopList_n (f:Z -> Z -> Z) (n:nat) (a : Z) (b : list Z) : list Z := match n, b with 
  | 0, _ => []
  | S p, []  => []
  | S p, h::q  => (f a h) :: (ZunopList_n f p a q)
end.

Lemma ZunopList_cons: forall f a h q, ZunopList f a (h :: q) = (f a h) :: (ZunopList f a q).
Proof. go. Qed.

Lemma ZunopList_map: forall f a l, ZunopList f a l = map (f a) l.
Proof. induction l ; go. Qed.

Lemma ZunopList_eq: forall f n a b,
  length b <= n ->
    ZunopList f a b = ZunopList_n f n a b.
Proof.
  induction n.
  destruct b ; go.
  intros a b Hlb.
  destruct b ; go.
  simpl in *.
  apply le_S_n in Hlb.
  f_equal.
  go.
Qed.

Lemma ZunopList_sliced: forall f n a b, slice n (ZunopList f a b) = ZunopList_n f n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; go. Qed.

Lemma ZunopList_slice : forall f n a b, slice n (ZunopList f a b) = ZunopList f a (slice n b).
Proof. induction n ; intros a b ; destruct b ; go. Qed.

Lemma ZunopList_length : forall f a b, length (ZunopList f a b) = (length b).
Proof. induction b; go. Qed.

Lemma ZunopList_tail : forall f n a b, tail n (ZunopList f a b) = ZunopList f a (tail n b).
Proof.
  induction n ; intros a b ; destruct b ; go.
Qed.
