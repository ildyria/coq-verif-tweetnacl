Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind".

Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Gen.Get_abcdef.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Gen.ABCDEF.
Require Import Recdef.

Section ScalarRec.

Open Scope Z.

Context {T : Type}.
Context {O : Ops T}.

Function abstract_fn_rev (m p:Z) (z a b c d e f x : T) {measure Z.to_nat m} : (T * T * T * T * T * T) :=
  if (m <=? 0)
    then (a,b,c,d,e,f)
    else 
    match (abstract_fn_rev (m - 1) p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := getbit (p - (m - 1)) z in
        (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma abstract_fn_rev_0 : forall p z a b c d e f x,
  abstract_fn_rev 0 p z a b c d e f x = (a,b,c,d,e,f).
Proof. move=> p z a b c d e f x ; reflexivity. Qed.

Lemma abstract_fn_rev_n : forall n p z a b c d e f x,
  0 < n ->
  abstract_fn_rev n p z a b c d e f x =
   match (abstract_fn_rev (n - 1) p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := getbit (p - (n - 1)) z in
        (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end.
Proof. move=> n p z a b c d e f x Hn.
rewrite abstract_fn_rev_equation.
assert((n <=? 0) = false).
by apply Z.leb_gt. flatten.
Qed.

Lemma abstract_fn_a : forall n p (z a b c d e f x : T),
  0 <= n ->
  fa (getbit (p - n) z)
   (get_a (abstract_fn_rev n p z a b c d e f x))
   (get_b (abstract_fn_rev n p z a b c d e f x))
   (get_c (abstract_fn_rev n p z a b c d e f x))
   (get_d (abstract_fn_rev n p z a b c d e f x))
   (get_e (abstract_fn_rev n p z a b c d e f x))
   (get_f (abstract_fn_rev n p z a b c d e f x))
   x
  =
  get_a (abstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite abstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (abstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma abstract_fn_b : forall n p (z a b c d e f x : T),
  0 <= n ->
  fb (getbit (p - n) z)
   (get_a (abstract_fn_rev n p z a b c d e f x))
   (get_b (abstract_fn_rev n p z a b c d e f x))
   (get_c (abstract_fn_rev n p z a b c d e f x))
   (get_d (abstract_fn_rev n p z a b c d e f x))
   (get_e (abstract_fn_rev n p z a b c d e f x))
   (get_f (abstract_fn_rev n p z a b c d e f x))
   x
  =
  get_b (abstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite abstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (abstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma abstract_fn_c : forall n p (z a b c d e f x : T),
  0 <= n ->
  fc (getbit (p - n) z)
   (get_a (abstract_fn_rev n p z a b c d e f x))
   (get_b (abstract_fn_rev n p z a b c d e f x))
   (get_c (abstract_fn_rev n p z a b c d e f x))
   (get_d (abstract_fn_rev n p z a b c d e f x))
   (get_e (abstract_fn_rev n p z a b c d e f x))
   (get_f (abstract_fn_rev n p z a b c d e f x))
   x
  =
  get_c (abstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite abstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (abstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma abstract_fn_d : forall n p (z a b c d e f x : T),
  0 <= n ->
  fd (getbit (p - n) z)
   (get_a (abstract_fn_rev n p z a b c d e f x))
   (get_b (abstract_fn_rev n p z a b c d e f x))
   (get_c (abstract_fn_rev n p z a b c d e f x))
   (get_d (abstract_fn_rev n p z a b c d e f x))
   (get_e (abstract_fn_rev n p z a b c d e f x))
   (get_f (abstract_fn_rev n p z a b c d e f x))
   x
  =
  get_d (abstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite abstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (abstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma abstract_fn_e : forall n p (z a b c d e f x : T),
  0 <= n ->
  fe (getbit (p - n) z)
   (get_a (abstract_fn_rev n p z a b c d e f x))
   (get_b (abstract_fn_rev n p z a b c d e f x))
   (get_c (abstract_fn_rev n p z a b c d e f x))
   (get_d (abstract_fn_rev n p z a b c d e f x))
   (get_e (abstract_fn_rev n p z a b c d e f x))
   (get_f (abstract_fn_rev n p z a b c d e f x))
   x
  =
  get_e (abstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite abstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (abstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma abstract_fn_f : forall n p (z a b c d e f x : T),
  0 <= n ->
  ff (getbit (p - n) z)
   (get_a (abstract_fn_rev n p z a b c d e f x))
   (get_b (abstract_fn_rev n p z a b c d e f x))
   (get_c (abstract_fn_rev n p z a b c d e f x))
   (get_d (abstract_fn_rev n p z a b c d e f x))
   (get_e (abstract_fn_rev n p z a b c d e f x))
   (get_f (abstract_fn_rev n p z a b c d e f x))
   x
  =
  get_f (abstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite abstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (abstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.

Close Scope Z.

End ScalarRec.
