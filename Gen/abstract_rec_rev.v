Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Gen.Get_abcdef.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Gen.ABCDEF.
Require Import Tweetnacl.Gen.step_gen.

Section ScalarRec.

Context {T : Type}.
Context {O : Ops T}.

Fixpoint abstract_rec_rev m p (z a b c d e f x : T) : (T * T * T * T * T * T)
  :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      match (abstract_rec_rev n p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := getbit (Z.of_nat (p - n)) z in
        (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end
  end.


Fixpoint abstract_rec (m : nat) (z a b c d e f x : T) : (T * T * T * T * T * T) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat n) z in
      abstract_rec n z 
        (fa r a b c d e f x)
        (fb r a b c d e f x)
        (fc r a b c d e f x)
        (fd r a b c d e f x)
        (fe r a b c d e f x)
        (ff r a b c d e f x)
        x
    end.

Arguments rec_fn_rev_acc [T] _ _ _.
Arguments rec_fn_rev [T] _ _.

Definition abstract_rev_fn (z x: T) (n:nat) (a b c d e f : T) := rec_fn_rev (step_gen z x) n (a,b,c,d,e,f).

Lemma abstract_rec_rev_equiv_rev_fn_p : forall n p z a b c d e f x,
  abstract_rec_rev n (p - 1) z a b c d e f x = rec_fn_rev_acc (step_gen z x) n p (a,b,c,d,e,f).
Proof.
  induction n => p z x a b c d e f.
  reflexivity.
  simpl.
  replace (p - n - 1) with (p - 1 - n).
  2: omega.
  remember((rec_fn_rev_acc (step_gen z f) n p (x, a, b, c, d, e))) as k.
  destruct k as (((((a0,b0),c0),d0),e0),f0).
  remember (abstract_rec_rev n (p - 1) z x a b c d e f ) as k'.
  destruct k' as (((((a1,b1),c1),d1),e1),f1).
  assert(IH := IHn p z x a b c d e f).
  go.
Qed.

Corollary abstract_rec_rev_equiv_rec_fn : forall n z a b c d e f x,
  abstract_rec_rev (S n) n z a b c d e f x = abstract_rev_fn z x (S n) a b c d e f.
Proof. intros. rewrite /abstract_rev_fn /rec_fn_rev -abstract_rec_rev_equiv_rev_fn_p.
replace (S n - 1) with n ; go.
Qed.

Arguments rec_fn [T] _ _ _.

Definition abstract_rec_fn (z x:T) (n:nat) (a b c d e f : T) := rec_fn (step_gen z x) n (a,b,c,d,e,f).

Lemma abstract_rec_equiv_rec_fn: forall n z a b c d e f x,
  abstract_rec n z a b c d e f x = abstract_rec_fn z x n a b c d e f.
Proof.
  induction n => z x a b c d e f.
  reflexivity.
  simpl.
  rewrite IHn /abstract_rec_fn.
  reflexivity.
Qed.


(* 
Lemma Zabstract_step_rev_a : forall n p (z a b c d e f x : Z),
  Zfa (Zgetbit (Z.of_nat (p - n)) z)
   (get_a (Zabstract_rec_rev n p z a b c d e f x))
   (get_b (Zabstract_rec_rev n p z a b c d e f x))
   (get_c (Zabstract_rec_rev n p z a b c d e f x))
   (get_d (Zabstract_rec_rev n p z a b c d e f x))
   (get_e (Zabstract_rec_rev n p z a b c d e f x))
   (get_f (Zabstract_rec_rev n p z a b c d e f x))
   x
  =
  get_a (Zabstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (Zabstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma Zabstract_step_rev_b : forall n p (z a b c d e f x : Z),
  Zfb (Zgetbit (Z.of_nat (p - n)) z)
   (get_a (Zabstract_rec_rev n p z a b c d e f x))
   (get_b (Zabstract_rec_rev n p z a b c d e f x))
   (get_c (Zabstract_rec_rev n p z a b c d e f x))
   (get_d (Zabstract_rec_rev n p z a b c d e f x))
   (get_e (Zabstract_rec_rev n p z a b c d e f x))
   (get_f (Zabstract_rec_rev n p z a b c d e f x))
   x
  =
  get_b (Zabstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (Zabstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma Zabstract_step_rev_c : forall n p (z a b c d e f x : Z),
  Zfc (Zgetbit (Z.of_nat (p - n)) z)
   (get_a (Zabstract_rec_rev n p z a b c d e f x))
   (get_b (Zabstract_rec_rev n p z a b c d e f x))
   (get_c (Zabstract_rec_rev n p z a b c d e f x))
   (get_d (Zabstract_rec_rev n p z a b c d e f x))
   (get_e (Zabstract_rec_rev n p z a b c d e f x))
   (get_f (Zabstract_rec_rev n p z a b c d e f x))
   x
  =
  get_c (Zabstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (Zabstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma Zabstract_step_rev_d : forall n p (z a b c d e f x : Z),
  Zfd (Zgetbit (Z.of_nat (p - n)) z)
   (get_a (Zabstract_rec_rev n p z a b c d e f x))
   (get_b (Zabstract_rec_rev n p z a b c d e f x))
   (get_c (Zabstract_rec_rev n p z a b c d e f x))
   (get_d (Zabstract_rec_rev n p z a b c d e f x))
   (get_e (Zabstract_rec_rev n p z a b c d e f x))
   (get_f (Zabstract_rec_rev n p z a b c d e f x))
   x
  =
  get_d (Zabstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (Zabstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma Zabstract_step_rev_e : forall n p (z a b c d e f x : Z),
  Zfe (Zgetbit (Z.of_nat (p - n)) z)
   (get_a (Zabstract_rec_rev n p z a b c d e f x))
   (get_b (Zabstract_rec_rev n p z a b c d e f x))
   (get_c (Zabstract_rec_rev n p z a b c d e f x))
   (get_d (Zabstract_rec_rev n p z a b c d e f x))
   (get_e (Zabstract_rec_rev n p z a b c d e f x))
   (get_f (Zabstract_rec_rev n p z a b c d e f x))
   x
  =
  get_e (Zabstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (Zabstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma Zabstract_step_rev_f : forall n p (z a b c d e f x : Z),
  Zff (Zgetbit (Z.of_nat (p - n)) z)
   (get_a (Zabstract_rec_rev n p z a b c d e f x))
   (get_b (Zabstract_rec_rev n p z a b c d e f x))
   (get_c (Zabstract_rec_rev n p z a b c d e f x))
   (get_d (Zabstract_rec_rev n p z a b c d e f x))
   (get_e (Zabstract_rec_rev n p z a b c d e f x))
   (get_f (Zabstract_rec_rev n p z a b c d e f x))
   x
  =
  get_f (Zabstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (Zabstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.
 *)
Open Scope Z.

End ScalarRec.