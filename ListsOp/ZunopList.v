Require Import Tweetnacl.Libs.Export.
Require Import Prelude.prelude.prelude.
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

Lemma ZunopList_eq_length: forall f n a b,
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

Open Scope Z.

Lemma ZunopList_eq_Zlength: forall f (n:nat) a b,
  Zlength b <= n ->
    ZunopList f a b = ZunopList_n f n a b.
Proof.
  intros.
  convert_length_to_Zlength ZunopList_eq_length.
Qed.

Lemma ZunopList_taked: forall f n a b, take n (ZunopList f a b) = ZunopList_n f n a b.
Proof. induction n ; intros a b ; simpl ; flatten ; go. Qed.

Lemma ZunopList_take : forall f n a b, take n (ZunopList f a b) = ZunopList f a (take n b).
Proof. induction n ; intros a b ; destruct b ; go. Qed.

Lemma ZunopList_length : forall f a b, length (ZunopList f a b) = (length b).
Proof. induction b; go. Qed.

Lemma ZunopList_Zlength : forall f a b, Zlength (ZunopList f a b) = (Zlength b).
Proof. induction b ; [|rewrite ZunopList_cons ; rewrite !Zlength_cons ; rewrite IHb] ; auto. Qed.

Lemma ZunopList_drop : forall f n a b, drop n (ZunopList f a b) = ZunopList f a (drop n b).
Proof. induction n ; intros a b ; destruct b ; go. Qed.
