Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Gen.Get_abcdef.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Gen.ABCDEF.
Require Import Tweetnacl.Gen.abstract_rec_rev.
Require Import Recdef.

Section Abstract_Rec_Rev.

Open Scope Z.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Lemma abstract_step_rev_a : forall n p (z : T') (a b c d e f x : T),
  fa (Getbit (Z.of_nat (p - n)) z)
   (get_a (abstract_rec_rev n p z a b c d e f x))
   (get_b (abstract_rec_rev n p z a b c d e f x))
   (get_c (abstract_rec_rev n p z a b c d e f x))
   (get_d (abstract_rec_rev n p z a b c d e f x))
   (get_e (abstract_rec_rev n p z a b c d e f x))
   (get_f (abstract_rec_rev n p z a b c d e f x))
   x
  =
  get_a (abstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma abstract_step_rev_b : forall n p (z : T') (a b c d e f x : T),
  fb (Getbit (Z.of_nat (p - n)) z)
   (get_a (abstract_rec_rev n p z a b c d e f x))
   (get_b (abstract_rec_rev n p z a b c d e f x))
   (get_c (abstract_rec_rev n p z a b c d e f x))
   (get_d (abstract_rec_rev n p z a b c d e f x))
   (get_e (abstract_rec_rev n p z a b c d e f x))
   (get_f (abstract_rec_rev n p z a b c d e f x))
   x
  =
  get_b (abstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma abstract_step_rev_c : forall n p (z : T') (a b c d e f x : T),
  fc (Getbit (Z.of_nat (p - n)) z)
   (get_a (abstract_rec_rev n p z a b c d e f x))
   (get_b (abstract_rec_rev n p z a b c d e f x))
   (get_c (abstract_rec_rev n p z a b c d e f x))
   (get_d (abstract_rec_rev n p z a b c d e f x))
   (get_e (abstract_rec_rev n p z a b c d e f x))
   (get_f (abstract_rec_rev n p z a b c d e f x))
   x
  =
  get_c (abstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma abstract_step_rev_d : forall n p (z : T') (a b c d e f x : T),
  fd (Getbit (Z.of_nat (p - n)) z)
   (get_a (abstract_rec_rev n p z a b c d e f x))
   (get_b (abstract_rec_rev n p z a b c d e f x))
   (get_c (abstract_rec_rev n p z a b c d e f x))
   (get_d (abstract_rec_rev n p z a b c d e f x))
   (get_e (abstract_rec_rev n p z a b c d e f x))
   (get_f (abstract_rec_rev n p z a b c d e f x))
   x
  =
  get_d (abstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma abstract_step_rev_e : forall n p (z : T') (a b c d e f x : T),
  fe (Getbit (Z.of_nat (p - n)) z)
   (get_a (abstract_rec_rev n p z a b c d e f x))
   (get_b (abstract_rec_rev n p z a b c d e f x))
   (get_c (abstract_rec_rev n p z a b c d e f x))
   (get_d (abstract_rec_rev n p z a b c d e f x))
   (get_e (abstract_rec_rev n p z a b c d e f x))
   (get_f (abstract_rec_rev n p z a b c d e f x))
   x
  =
  get_e (abstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Lemma abstract_step_rev_f : forall n p (z : T') (a b c d e f x : T),
  ff (Getbit (Z.of_nat (p - n)) z)
   (get_a (abstract_rec_rev n p z a b c d e f x))
   (get_b (abstract_rec_rev n p z a b c d e f x))
   (get_c (abstract_rec_rev n p z a b c d e f x))
   (get_d (abstract_rec_rev n p z a b c d e f x))
   (get_e (abstract_rec_rev n p z a b c d e f x))
   (get_f (abstract_rec_rev n p z a b c d e f x))
   x
  =
  get_f (abstract_rec_rev (S n) p z a b c d e f x).
Proof.
intros; simpl; remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0); reflexivity.
Qed.

Close Scope Z.

End Abstract_Rec_Rev.