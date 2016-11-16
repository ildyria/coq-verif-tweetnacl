Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition in_eq: forall {A: Type} (a:A) l, In a (a::l) :=
  fun A a l => or_introl eq_refl.

Definition Forall_forall: forall {A : Type} (P : A -> Prop) (l : list A),
       Forall P l <-> (forall x : A, In x l -> P x)   :=
fun (A : Type) (P : A -> Prop) (l : list A) =>
conj
  (fun H : Forall P l =>
   Forall_ind (fun l0 : list A => forall x : A, In x l0 -> P x)
     (fun (x : A) (H0 : In x nil) => False_ind (P x) H0)
     (fun (x : A) (l0 : list A) (H0 : P x) (_ : Forall P l0)
        (IHForall : forall x0 : A, In x0 l0 -> P x0) (x0 : A)
        (H2 : In x0 (x :: l0)) =>
      or_ind
        (fun H3 : x = x0 =>
         eq_ind_r (fun x1 : A => P x1 -> P x0) (fun H4 : P x0 => H4) H3 H0)
        (fun H3 : In x0 l0 =>
         (fun H4 : In x0 l0 -> P x0 => (fun H5 : P x0 => H5) (H4 H3))
           (IHForall x0)) H2) H)
  (list_ind
     (fun l0 : list A => (forall x : A, In x l0 -> P x) -> Forall P l0)
     (fun _ : forall x : A, In x nil -> P x => Forall_nil P)
     (fun (a : A) (l0 : list A)
        (IHl : (forall x : A, In x l0 -> P x) -> Forall P l0)
        (H : forall x : A, In x (a :: l0) -> P x) =>
      (fun H0 : forall x : A, In x l0 -> P x =>
       (fun H1 : forall x : A, In x l0 -> P x =>
        (fun H2 : Forall P l0 =>
         (fun H3 : A =>
          (fun X : A =>
           (fun H4 : In X (a :: l0) -> P X =>
            (fun (_ : a = X -> P X)
               (_ : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                       match l1 with
                       | nil => False
                       | b :: m => b = a0 \/ In a0 m
                       end) X l0 -> P X) =>
             Forall_cons a (H a (in_eq a l0)) H2)
              (fun H5 : a = X => H4 (or_introl H5))
              (fun
                 H5 : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                         match l1 with
                         | nil => False
                         | b :: m => b = a0 \/ In a0 m
                         end) X l0 => H4 (or_intror H5))) (H X)) H3) a)
          (IHl H1)) H0)
        (fun (x : A) (H0 : In x l0) =>
         (fun H1 : In x (a :: l0) -> P x =>
          (fun (_ : a = x -> P x)
             (H3 : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                      match l1 with
                      | nil => False
                      | b :: m => b = a0 \/ In a0 m
                      end) x l0 -> P x) => (fun H4 : P x => H4) (H3 H0))
            (fun H2 : a = x => H1 (or_introl H2))
            (fun
               H2 : (fix In (a0 : A) (l1 : list A) {struct l1} : Prop :=
                       match l1 with
                       | nil => False
                       | b :: m => b = a0 \/ In a0 m
                       end) x l0 => H1 (or_intror H2))) (H x))) l).

Lemma Forall_forall1: forall {A : Type} (P : A -> Prop) (l : list A),
       Forall P l -> (forall x : A, In x l -> P x).
Proof.
intros until 1.
destruct (@Forall_forall A P l).
apply H0. auto.
Defined.

Lemma Forall_cons': forall {A : Type} (P : A -> Prop) (a: A) (l : list A),
       Forall P (a::l) <-> P a /\ Forall P l.
Proof.
intros ; split ; intro.
rewrite Forall_forall in H.
split.
apply H ; simpl ; auto.
rewrite Forall_forall.
intros ; apply H ; simpl ; auto.
destruct H.
apply Forall_cons ; auto.
Qed.


(*
Lemma Zcompare_refl: forall n, Z.compare n n = Eq.
Proof.
intros.
destruct n; simpl.
apply eq_refl.
unfold Pos.compare.
induction p; simpl; auto.
unfold Pos.compare.
induction p; simpl; auto.
Defined.

Lemma Zle_refl: forall n, Z.le n n.
Proof.
intros.
unfold Z.le. rewrite Zcompare_refl. intro; discriminate.
Defined.

Lemma Zle_max_l: forall n m : Z, n <= Z.max n m.
Proof.
intros.
unfold Z.max.
unfold Z.le.
destruct (n?=m) eqn:H.
rewrite Zcompare_refl; intro; discriminate.
rewrite H. intro; discriminate.
rewrite Zcompare_refl; intro; discriminate.
Defined.

Definition Pos_compare_cont_antisym : 
  forall (p q : positive) (c : comparison),
       eq (CompOpp (Pos.compare_cont c p q))
         (Pos.compare_cont (CompOpp c) q p ) := 
fun (p q : positive) (c : comparison) =>
positive_ind
  (fun p0 : positive =>
   forall (q0 : positive) (c0 : comparison),
   CompOpp (Pos.compare_cont c0 p0 q0) =
   Pos.compare_cont (CompOpp c0) q0 p0)
  (fun (p0 : positive)
     (IHp : forall (q0 : positive) (c0 : comparison),
            CompOpp (Pos.compare_cont c0 p0 q0) =
            Pos.compare_cont (CompOpp c0) q0 p0)
     (q0 : positive) =>
   match
     q0 as p1
     return
       (forall c0 : comparison,
        CompOpp (Pos.compare_cont c0 p0~1 p1) =
        Pos.compare_cont (CompOpp c0) p1 p0~1)
   with
   | (q1~1)%positive =>
       fun c0 : comparison => IHp q1 c0
   | (q1~0)%positive =>
       fun c0 : comparison => IHp q1 Gt
   | 1%positive => fun c0 : comparison => eq_refl
   end)
  (fun (p0 : positive)
     (IHp : forall (q0 : positive) (c0 : comparison),
            CompOpp (Pos.compare_cont c0 p0 q0) =
            Pos.compare_cont (CompOpp c0) q0 p0)
     (q0 : positive) =>
   match
     q0 as p1
     return
       (forall c0 : comparison,
        CompOpp (Pos.compare_cont c0 p0~0 p1) =
        Pos.compare_cont (CompOpp c0) p1 p0~0)
   with
   | (q1~1)%positive =>
       fun c0 : comparison => IHp q1 Lt
   | (q1~0)%positive =>
       fun c0 : comparison => IHp q1 c0
   | 1%positive => fun c0 : comparison => eq_refl
   end)
  (fun q0 : positive =>
   match
     q0 as p0
     return
       (forall c0 : comparison,
        CompOpp (Pos.compare_cont c0 1 p0) =
        Pos.compare_cont (CompOpp c0) p0 1)
   with
   | (q1~1)%positive =>
       fun c0 : comparison => eq_refl
   | (q1~0)%positive =>
       fun c0 : comparison => eq_refl
   | 1%positive => fun c0 : comparison => eq_refl
   end) p q c.

Definition Pos_compare_antisym: 
  forall p q : positive,
       eq (Pos.compare q p) (CompOpp (Pos.compare p q)) :=
  fun p q : positive =>
eq_ind_r (fun c : comparison => eq (Pos.compare_cont Eq q p) c) eq_refl
  (Pos_compare_cont_antisym p q Eq).

Lemma Pos_compare_absurd:
  forall x y c, (eq (Pos.compare_cont c x y) Eq) -> c=Eq.
Proof.
induction x; destruct y; simpl; intros; eauto; try discriminate.
apply IHx in H; discriminate.
apply IHx in H; discriminate.
Defined.

Lemma Pos_compare_cont_eq: 
  forall x y c, eq (Pos.compare_cont c x y) Eq -> eq x y.
Proof.
induction x; destruct y; simpl; intros; auto; try discriminate.
f_equal. eauto.
apply Pos_compare_absurd in H; inversion H.
apply Pos_compare_absurd in H; inversion H.
f_equal. eauto.
Defined.

Lemma Pos_compare_eq:
  forall x y, eq (Pos.compare x y) Eq -> eq x y.
Proof.
intros.
apply Pos_compare_cont_eq in H; auto.
Defined.

Lemma Zmax_comm: forall n m, Z.max n m = Z.max m n.
Proof.
destruct n, m; simpl; try apply eq_refl.
*
 unfold Z.max; simpl.
 rename p0 into q.
 rewrite Pos_compare_antisym.
 destruct (Pos.compare q p) eqn:?; simpl; try reflexivity.
 apply Pos_compare_eq in Heqc.
 apply f_equal. symmetry; auto.
*
 unfold Z.max; simpl.
 rename p0 into q.
 rewrite Pos_compare_antisym.
 destruct (Pos.compare q p) eqn:?; simpl; try reflexivity.
 apply Pos_compare_eq in Heqc.
 apply f_equal. symmetry; auto.
Defined.

Lemma Zle_max_r: forall n m : Z, m <= Z.max n m.
Proof.
intros.
rewrite Z.max_comm. apply Zle_max_l.
Defined.
*)