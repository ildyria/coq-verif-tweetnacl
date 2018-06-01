Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Mid.ScalarMult_step_gen.

Section ScalarRec.

Variable Zfa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zgetbit : Z -> Z -> Z.

Fixpoint Zabstract_rec_rev m p (z a b c d e f x : Z) : (Z * Z * Z * Z * Z * Z)
  :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      match (Zabstract_rec_rev n p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := Zgetbit (Z.of_nat (p - n)) z in
        (Zfa r a b c d e f x,
        Zfb r a b c d e f x,
        Zfc r a b c d e f x,
        Zfd r a b c d e f x,
        Zfe r a b c d e f x,
        Zff r a b c d e f x)
      end
  end.


(* Proof of the Currying of the function  *)
Definition Zstep_gen :=  Zstep_gen Zfa Zfb Zfc Zfd Zfe Zff Zgetbit.

Arguments rec_fn_rev_acc [T] _ _ _.
Arguments rec_fn_rev [T] _ _.

Definition abstract_rec_fn (z x: Z) (n:nat) (a b c d e f : Z) := rec_fn_rev (Zstep_gen z x) n (a,b,c,d,e,f).

Lemma abstract_rec_rev_equiv_recfn_p: forall n p z a b c d e f x,
  Zabstract_rec_rev n (p - 1) z a b c d e f x = rec_fn_rev_acc (Zstep_gen z x) n p (a,b,c,d,e,f).
Proof.
  induction n => p z x a b c d e f.
  reflexivity.
  simpl.
  replace (p - n - 1) with (p - 1 - n).
  2: omega.
  remember((rec_fn_rev_acc (Zstep_gen z f) n p (x, a, b, c, d, e))) as k.
  destruct k as (((((a0,b0),c0),d0),e0),f0).
  remember (Zabstract_rec_rev n (p - 1) z x a b c d e f ) as k'.
  destruct k' as (((((a1,b1),c1),d1),e1),f1).
  assert(IH := IHn p z x a b c d e f).
  go.
Qed.

Corollary abstract_rec_rev_equiv_rec_fn : forall n z a b c d e f x,
  Zabstract_rec_rev (S n) n z a b c d e f x = abstract_rec_fn z x (S n) a b c d e f.
Proof. intros. rewrite /abstract_rec_fn /rec_fn_rev -abstract_rec_rev_equiv_recfn_p.
replace (S n - 1) with n ; go.
Qed.


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

Open Scope Z.

End ScalarRec.