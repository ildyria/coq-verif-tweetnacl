Require Export Tools.
Require Export notations.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZopList (f:Z -> Z -> Z) (a b : list Z) : list Z := match a,b with
  | [], [] => []
  | [], q => map (f 0%Z) q
  | q, [] => map (fun x => (f x 0%Z)) q
  | h1::q1,h2::q2 => (f h1 h2) :: ZopList f q1 q2
end.

Notation "F ( A , B )" := (ZopList F A B) (at level 60, right associativity).

Fixpoint ZopList_n (f:Z -> Z -> Z) (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => (f 0%Z h) :: (ZopList_n f p [] q)
  | S p, h::q, []  => (f h 0%Z) :: (ZopList_n f p q [])
  | S p, h1::q1, h2::q2 => (f h1 h2) :: (ZopList_n f p q1 q2)
end.

Lemma ZopList_empty1: forall f h q, ZopList f (h :: q) [] = (f h 0%Z) :: (ZopList f q []).
Proof. induction q ; go. Qed.

Lemma ZopList_empty2: forall f h q, ZopList f [] (h :: q) = (f 0%Z h) :: (ZopList f [] q).
Proof. induction q ; go. Qed.

Lemma ZopList_eq: forall f n a b,
  length a <= n ->
  length b <= n ->
    ZopList f a b = ZopList_n f n a b.
Proof.
  induction n.
  destruct a, b ; go.
  intros a b Hla Hlb.
  destruct a, b ; go.
  rewrite ZopList_empty2 ; simpl ZopList_n ; f_equal ; apply IHn ; go.
  simpl in Hla ; apply le_S_n in Hla.
  simpl ZopList ; simpl ZopList_n; f_equal; rewrite <- IHn; destruct a ; go.
  simpl in Hla, Hlb ; apply le_S_n in Hla ; apply le_S_n in Hlb.
  simpl ; f_equal ; apply IHn ; go.
Qed.

Lemma map_f_0: forall f q, map (f 0%Z) q = ZopList f [] q.
Proof. induction q; go. Qed.

Lemma map_f_0': forall f q, map (fun x => f x 0%Z) q = ZopList f q [].
Proof. induction q; go. Qed.

Lemma ZopList_sliced: forall f n a b, slice n (ZopList f a b) = ZopList_n f n a b.
Proof.
  induction n ; intros a b ; simpl ; flatten ; go ; try inv Eq ; rewrite <- IHn ; f_equal ;   [rewrite map_f_0 | rewrite map_f_0']; go.
Qed.

Lemma ZopList_slice : forall f n a b, slice n (ZopList f a b) = ZopList f (slice n a) (slice n b).
Proof.
  induction n ; intros a b ; destruct a; destruct b ; go ; 
  simpl; repeat rewrite map_f_0 ; repeat rewrite map_f_0' ; rewrite IHn; destruct n; go.
Qed.

Lemma ZopList_length_max : forall f a b, length (ZopList f a b) = max (length a) (length b).
Proof.
  induction a; destruct b ; go ; 
   simpl ; rewrite map_length ; reflexivity.
Qed.

Lemma ZopList_length : forall f a b, length (ZopList f a b) = length a \/ length (ZopList f a b) = length b.
Proof.
  intros f a b.
  rewrite ZopList_length_max.
  assert(Hl: length a < length b \/ length a = length b \/ length a > length b) by omega.
  case Hl ; intros.
  right; apply Max.max_r ; go.
  case H ; intros.
  right; apply Max.max_r ; go.
  left; apply Max.max_l ; go.
Qed.

Definition f_comm (f: Z -> Z -> Z) := forall x y, f x y = f y x.
Definition f_0_neutre (f: Z -> Z -> Z) := forall x, f x 0%Z = x.
Definition f_neutre_0 (f: Z -> Z -> Z) := forall x, f 0%Z x = x.
Definition f_assoc (f: Z -> Z -> Z) := forall x y z, f (f x y) z = f x (f y z).

Lemma ZopList_comm: forall f a b, f_comm f -> ZopList f a b = ZopList f b a.
Proof.
  induction a, b ; intros H ; try reflexivity ; 
  simpl ; f_equal; go ; apply map_ext ; intros x Hx ; rewrite H ;  reflexivity.
Qed.

Lemma ZopList_nil_simpl_l: forall f a, ZopList f a [] = map (fun x : Z => f x 0%Z) a.
Proof.
  induction a; go.
Qed.

Lemma ZopList_nil_simpl_r: forall f a, ZopList f [] a = map (f 0%Z) a.
Proof.
  induction a; go.
Qed.

Lemma ZopList_nil_r: forall f a, f_0_neutre f -> ZopList f a [] = a.
Proof.
  intros ; go.
  rewrite ZopList_nil_simpl_l.
  replace (map (fun x : ℤ => f x 0%Z) a) with (map (fun x : ℤ => x) a).
  apply map_id.
  apply map_ext ; go.
Qed.

Lemma ZopList_nil_l: forall f a, f_neutre_0 f ->  ZopList f [] a = a.
Proof.
  intros ; go.
  rewrite ZopList_nil_simpl_r ; go.
  replace (map (f 0%Z) a) with (map (fun x : ℤ => x) a) ; go.
  rewrite map_id ; go.
  apply map_ext ; go.
Qed.


Lemma ZopList_assoc : forall f a b c, f_assoc f -> f_neutre_0 f ->  f_0_neutre f ->  ZopList f (ZopList f a b) c = ZopList f a (ZopList f b c).
Proof.
  induction a, b, c ; intros ; go.
  repeat rewrite ZopList_nil_l ; auto.
  repeat rewrite ZopList_nil_l ; auto.
  repeat rewrite ZopList_nil_l ; auto.
  repeat rewrite ZopList_nil_r ; auto.
  f_equal; [apply ZopList_nil_r | rewrite ZopList_nil_l] ; auto.
  repeat rewrite ZopList_nil_r ; auto.
  simpl ; f_equal ; auto.
Qed.

Lemma ZopList_tail : forall f n a b, tail n (ZopList f a b) = ZopList f (tail n a) (tail n b).
Proof.
  induction n ; intros a b ; destruct a; destruct b ; go.
  - simpl tail.
    rewrite ZopList_nil_simpl_r ; auto.
    rewrite map_tail ; reflexivity.
  - simpl.
    rewrite ZopList_nil_simpl_l ; auto.
    rewrite map_tail ; reflexivity.
Qed.
