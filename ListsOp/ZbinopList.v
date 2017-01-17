Require Import Libs.Export.
Import ListNotations.

Ltac ind_destr_destr n a b :=
  induction n ; destruct a ; destruct b ; boum.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZbinopList (f:Z -> Z -> Z) (a b : list Z) : list Z := match a,b with
  | [], [] => []
  | [], q => map (f 0%Z) q
  | q, [] => map (fun x => (f x 0%Z)) q
  | h1::q1,h2::q2 => (f h1 h2) :: ZbinopList f q1 q2
end.

Notation "F ( A , B )" := (ZbinopList F A B) (at level 60, right associativity).

Fixpoint ZbinopList_n (f:Z -> Z -> Z) (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => (f 0%Z h) :: (ZbinopList_n f p [] q)
  | S p, h::q, []  => (f h 0%Z) :: (ZbinopList_n f p q [])
  | S p, h1::q1, h2::q2 => (f h1 h2) :: (ZbinopList_n f p q1 q2)
end.

Lemma ZbinopList_empty1: forall f h q, ZbinopList f (h :: q) [] = (f h 0%Z) :: (ZbinopList f q []).
Proof. ind_boum q. Qed.

Lemma ZbinopList_empty2: forall f h q, ZbinopList f [] (h :: q) = (f 0%Z h) :: (ZbinopList f [] q).
Proof. ind_boum q. Qed.

Lemma ZbinopList_eq: forall f n a b,
  length a <= n ->
  length b <= n ->
    ZbinopList f a b = ZbinopList_n f n a b.
Proof.
  ind_destr_destr n a b ; 
  repeat match goal with
    | _ => progress boum
    | |- _ :: _ = _ :: _ => progress f_equal
    | [ H : context[length] |- _ ] => simpl in H ; apply le_S_n in H
    | _ => progress rewrite ZbinopList_empty2
    | _ => progress apply IHn
    | _ => progress simpl ZbinopList_n
    | _ => progress simpl ZbinopList
    | _ => progress rewrite <- IHn
    | [ |- map _ ?a = _ ] => destr_boum a
  end.
Qed.

Lemma ZbinopList_map_l: forall f a, ZbinopList f a [] = map (fun x : Z => f x 0%Z) a.
Proof. ind_boum a. Qed.

Lemma ZbinopList_map_r: forall f a, ZbinopList f [] a = map (f 0%Z) a.
Proof. ind_boum a. Qed.

Lemma ZbinopList_sliced: forall f n a b, slice n (ZbinopList f a b) = ZbinopList_n f n a b.
Proof. ind_destr_destr n a b ; simpl ; flatten ; go ; try inv Eq ; rewrite <- IHn ; f_equal ;   [rewrite ZbinopList_map_r | rewrite ZbinopList_map_l]; go.
Qed.

Lemma ZbinopList_slice : forall f n a b, slice n (ZbinopList f a b) = ZbinopList f (slice n a) (slice n b).
Proof.
ind_destr_destr n a b ; simpl; repeat rewrite <- ZbinopList_map_l ; repeat rewrite <- ZbinopList_map_r ; rewrite IHn; destruct n; go.
Qed.

Lemma ZbinopList_length_max : forall f a b, length (ZbinopList f a b) = max (length a) (length b).
Proof.
  induction a; destruct b ; go ; simpl ; rewrite map_length ; reflexivity.
Qed.

Lemma ZbinopList_length : forall f a b, length (ZbinopList f a b) = length a \/ length (ZbinopList f a b) = length b.
Proof.
  intros f a b.
  rewrite ZbinopList_length_max.
  assert(Hl: length a < length b \/ length a = length b \/ length a > length b) by omega.
  repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | _ => right; apply Max.max_r ; go ; fail
    | _ => left; apply Max.max_l ; go ; fail
  end.
Qed.

Definition f_comm (f: Z -> Z -> Z) := forall x y, f x y = f y x.
Definition f_0_neutre (f: Z -> Z -> Z) := forall x, f x 0%Z = x.
Definition f_neutre_0 (f: Z -> Z -> Z) := forall x, f 0%Z x = x.
Definition f_assoc (f: Z -> Z -> Z) := forall x y z, f (f x y) z = f x (f y z).

Lemma ZbinopList_comm: forall f a b, f_comm f -> ZbinopList f a b = ZbinopList f b a.
Proof.
  induction a, b ;
  repeat match goal with
    | _ => progress intros
    | _ => reflexivity
    | _ => simpl ; f_equal ; go ; apply map_ext
    | [ H : f_comm _ |- _ ] => rewrite H
  end.
Qed.

Lemma ZbinopList_nil_r: forall f a, f_0_neutre f -> ZbinopList f a [] = a.
Proof.
  intros ; go.
  rewrite ZbinopList_map_l.
  replace (map (fun x : ℤ => f x 0%Z) a) with (map (fun x : ℤ => x) a).
  apply map_id.
  apply map_ext ; go.
Qed.

Lemma ZbinopList_nil_l: forall f a, f_neutre_0 f ->  ZbinopList f [] a = a.
Proof.
  intros ; go.
  rewrite ZbinopList_map_r ; go.
  replace (map (f 0%Z) a) with (map (fun x : ℤ => x) a) ; go.
  rewrite map_id ; go.
  apply map_ext ; go.
Qed.


Lemma ZbinopList_assoc : forall f a b c, f_assoc f -> f_neutre_0 f ->  f_0_neutre f ->  ZbinopList f (ZbinopList f a b) c = ZbinopList f a (ZbinopList f b c).
Proof.
  induction a, b, c ;
  repeat match goal with
   | _ => progress intros
   | _ => progress go
   | _ => rewrite ZbinopList_nil_r
   | _ => rewrite ZbinopList_nil_l
   | _ => simpl ; f_equal
   end.
Qed.

Lemma ZbinopList_tail : forall f n a b, tail n (ZbinopList f a b) = ZbinopList f (tail n a) (tail n b).
Proof.
  ind_destr_destr n a b; simpl tail ; [rewrite ZbinopList_map_r | rewrite ZbinopList_map_l] ; auto ; rewrite map_tail ; reflexivity.
Qed.
