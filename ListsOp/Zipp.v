Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.Export.

Ltac ind_destr_destr n a b :=
  induction n ; destruct a ; destruct b ; boum.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint Zipp (f:Z -> Z -> Z) (a b : list Z) : list Z := match a,b with
  | [], [] => []
  | [], q => map (f 0%Z) q
  | q, [] => map (fun x => (f x 0%Z)) q
  | h1::q1,h2::q2 => (f h1 h2) :: Zipp f q1 q2
end.

Notation "F ( A , B )" := (Zipp F A B) (at level 60, right associativity).
(*
Fixpoint Zipp_n (f:Z -> Z -> Z) (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => (f 0%Z h) :: (Zipp_n f p [] q)
  | S p, h::q, []  => (f h 0%Z) :: (Zipp_n f p q [])
  | S p, h1::q1, h2::q2 => (f h1 h2) :: (Zipp_n f p q1 q2)
end.
*)
Lemma Zipp_nil1: forall f h q, Zipp f (h :: q) [] = (f h 0%Z) :: (Zipp f q []).
Proof. ind_boum q. Qed.

Lemma Zipp_nil2: forall f h q, Zipp f [] (h :: q) = (f 0%Z h) :: (Zipp f [] q).
Proof. ind_boum q. Qed.
(*
Lemma Zipp_eq_length: forall f n a b,
  length a <= n ->
  length b <= n ->
    Zipp f a b = Zipp_n f n a b.
Proof.
  ind_destr_destr n a b ; 
  repeat match goal with
    | _ => progress boum
    | |- _ :: _ = _ :: _ => progress f_equal
    | [ H : context[length] |- _ ] => simpl in H ; apply le_S_n in H
    | _ => progress apply IHn
    | _ => progress simpl Zipp_n
    | _ => progress simpl Zipp
    | _ => progress rewrite <- IHn
    | [ |- map _ ?a = _ ] => destr_boum a
  end.
Qed.
*)
Open Scope Z.
(*
Lemma Zipp_n_length : forall f (n:nat) (a b : list Z), length (Zipp_n f n a b) = min n (max (length a) (length b)).
Proof. ind_destr_destr n a b ; simpl ; rewrite IHn; [|rewrite max_l] ; boum. Qed.

Lemma Zipp_eq_Zlength: forall f (n:nat) a b,
  Zlength a <= n ->
  Zlength b <= n ->
    Zipp f a b = Zipp_n f n a b.
Proof. convert_length_to_Zlength Zipp_eq_length. Qed.

Lemma Zipp_n_Zlength : forall f (n:nat) (a b : list Z), Zlength (Zipp_n f n a b) = Zmin n (Zmax (Zlength a) (Zlength b)).
Proof. convert_length_to_Zlength Zipp_n_length.
rewrite Nat2Z.inj_min.
rewrite Nat2Z.inj_max.
reflexivity.
Qed.
*)
Lemma Zipp_map_l: forall f a, Zipp f a [] = map (fun x : Z => f x 0%Z) a.
Proof. ind_boum a. Qed.

Lemma Zipp_map_r: forall f a, Zipp f [] a = map (f 0%Z) a.
Proof. ind_boum a. Qed.
(*
Lemma Zipp_taked: forall f n a b, take n (Zipp f a b) = Zipp_n f n a b.
Proof. ind_destr_destr n a b ; simpl ; flatten ; go ; try inv Eq ; rewrite <- IHn ; f_equal ;   [rewrite Zipp_map_r | rewrite Zipp_map_l]; go. Qed.
*)
Lemma Zipp_take : forall f n a b, take n (Zipp f a b) = Zipp f (take n a) (take n b).
Proof. ind_destr_destr n a b => //=; rewrite -?Zipp_map_l -?Zipp_map_r IHn; destruct n; go. Qed.

Lemma Zipp_length_max : forall f a b, length (Zipp f a b) = max (length a) (length b).
Proof. induction a ; destruct b ; go => //= ; rewrite map_length ; reflexivity. Qed.

Lemma Zipp_Zlength_max : forall f a b, Zlength (Zipp f a b) = Z.max (Zlength a) (Zlength b).
Proof.
  induction a as [|h a IHl]; destruct b ; go ; simpl;
  try assert(Ha := Zlength_pos a);
  try assert(Hb := Zlength_pos b).

  rewrite ?Zlength_cons Zlength_map Z.max_r; try reflexivity.
  rewrite Zlength_nil; omega.

  rewrite ?Zlength_cons Zlength_map Z.max_l ; try reflexivity.
  rewrite Zlength_nil; omega.

  rewrite ?Zlength_cons IHl.
  apply Z.succ_max_distr.
Qed.

Lemma Zipp_length : forall f a b, length (Zipp f a b) = length a \/ length (Zipp f a b) = length b.
Proof.
  intros f a b.
  rewrite Zipp_length_max.
  assert(Hl: length a < length b \/ length a = length b \/ length a > length b) by omega.
  repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | _ => right; apply Max.max_r ; go ; fail
    | _ => left; apply Max.max_l ; go ; fail
  end.
Qed.

Lemma Zipp_Zlength : forall f a b, Zlength (Zipp f a b) = Zlength a \/ Zlength (Zipp f a b) = Zlength b.
Proof.
  intros f a b.
  rewrite Zipp_Zlength_max.
  assert(Hl: Zlength a < Zlength b \/ Zlength a = Zlength b \/ Zlength a > Zlength b) by omega.
  repeat match goal with
    | [ H : _ \/ _ |- _ ] => destruct H
    | _ => right; apply Z.max_r ; go ; fail
    | _ => left; apply Z.max_l ; go ; fail
  end.
Qed.
(*
Lemma Zipp_n_nth_length : forall f (n : nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  Zipp_n f (S n) a b = (Zipp_n f n a b) ++ [f (nth n a 0) (nth n b 0)].
Proof.
  induction n; intros.
  simpl ; flatten ; simpl ; simpl in H0 ; try omega ; try reflexivity.
  do 2 (destruct a ; destruct b ;
        try match goal with
         | [H : context[length] |- _ ] => simpl in H ; omega
        end).
  repeat rewrite nth_lookup.
  unfold lookup ; unfold list_lookup.
  rewrite <- (nth_lookup (z1 :: a) n).
  rewrite <- (nth_lookup (z2 :: b) n).
  change (Zipp_n f (S (S n)) (z :: z1 :: a) (z0 :: z2 :: b))
  with (f z z0 :: Zipp_n f (S n) (z1 :: a) (z2 :: b)).
  rewrite IHn by (simpl in *; omega).
  simpl Zipp_n.
  rewrite app_comm_cons ; reflexivity.
Qed.

Lemma Zipp_n_nth_Zlength : forall f (n : nat) (a b : list Z),
  Zlength a = Zlength b ->
  n < Zlength a ->
  Zipp_n f (S n) a b = (Zipp_n f n a b) ++ [f (nth n a 0) (nth n b 0)].
Proof. convert_length_to_Zlength Zipp_n_nth_length. Qed.
*)

Lemma Zipp_nth_length : forall f (n : nat) (a b : list Z),
  length a = length b ->
  (n < length a)%nat ->
  nth n (Zipp f a b) (f 0 0) = f (nth n a 0) (nth n b 0).
Proof. induction n; destruct a,b ; simpl ; intros ; flatten ; go. Qed.

Definition f_comm (f: Z -> Z -> Z) := forall x y, f x y = f y x.
Definition f_0_neutral (f: Z -> Z -> Z) := forall x, f x 0%Z = x.
Definition f_neutral_0 (f: Z -> Z -> Z) := forall x, f 0%Z x = x.
Definition f_assoc (f: Z -> Z -> Z) := forall x y z, f (f x y) z = f x (f y z).

Lemma Zipp_comm: forall f a b, f_comm f -> Zipp f a b = Zipp f b a.
Proof.
  induction a, b ;
  repeat match goal with
    | _ => progress intros
    | _ => reflexivity
    | _ => simpl ; f_equal ; go ; apply map_ext
    | [ H : f_comm _ |- _ ] => rewrite H
  end.
Qed.

Lemma Zipp_nil_r: forall f a, f_0_neutral f -> Zipp f a [] = a.
Proof.
  intros ; go.
  rewrite Zipp_map_l.
  replace (map (fun x : ℤ => f x 0%Z) a) with (map (fun x : ℤ => x) a).
  apply map_id.
  apply map_ext ; go.
Qed.

Lemma Zipp_nil_l: forall f a, f_neutral_0 f ->  Zipp f [] a = a.
Proof.
  intros ; go.
  rewrite Zipp_map_r ; go.
  replace (map (f 0%Z) a) with (map (fun x : ℤ => x) a) ; go.
  rewrite map_id ; go.
  apply map_ext ; go.
Qed.


Lemma Zipp_assoc : forall f a b c, f_assoc f -> f_neutral_0 f ->  f_0_neutral f ->  Zipp f (Zipp f a b) c = Zipp f a (Zipp f b c).
Proof.
  induction a, b, c ;
  repeat match goal with
   | _ => progress intros
   | _ => progress go
   | _ => rewrite Zipp_nil_r
   | _ => rewrite Zipp_nil_l
   | _ => simpl ; f_equal
   end.
Qed.

Lemma Zipp_drop : forall f n a b, drop n (Zipp f a b) = Zipp f (drop n a) (drop n b).
Proof.
  ind_destr_destr n a b; simpl drop ; [rewrite Zipp_map_r | rewrite Zipp_map_l] ; auto ; rewrite map_drop ; reflexivity.
Qed.

Close Scope Z.