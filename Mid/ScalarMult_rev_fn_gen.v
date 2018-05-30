Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind".

Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Recdef.

Section ScalarRec.

Open Scope Z.

Variable Zfa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zgetbit : Z -> Z -> Z.

Function Zabstract_fn_rev (m p:Z) (z a b c d e f x : Z) {measure Z.to_nat m} : (Z * Z * Z * Z * Z * Z) :=
  if (m <=? 0)
    then (a,b,c,d,e,f)
    else 
    match (Zabstract_fn_rev (m - 1) p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := Zgetbit (p - (m - 1)) z in
        (Zfa r a b c d e f x,
        Zfb r a b c d e f x,
        Zfc r a b c d e f x,
        Zfd r a b c d e f x,
        Zfe r a b c d e f x,
        Zff r a b c d e f x)
      end.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma Zabstract_fn_rev_0 : forall p z a b c d e f x,
  Zabstract_fn_rev 0 p z a b c d e f x = (a,b,c,d,e,f).
Proof. move=> p z a b c d e f x ; reflexivity. Qed.

Lemma Zabstract_fn_rev_n : forall n p z a b c d e f x,
  0 < n ->
  Zabstract_fn_rev n p z a b c d e f x =
   match (Zabstract_fn_rev (n - 1) p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := Zgetbit (p - (n - 1)) z in
        (Zfa r a b c d e f x,
        Zfb r a b c d e f x,
        Zfc r a b c d e f x,
        Zfd r a b c d e f x,
        Zfe r a b c d e f x,
        Zff r a b c d e f x)
      end.
Proof. move=> n p z a b c d e f x Hn.
rewrite Zabstract_fn_rev_equation.
assert((n <=? 0) = false).
by apply Z.leb_gt. flatten.
Qed.

Lemma Zabstract_fn_a : forall n p (z a b c d e f x : Z),
  0 <= n ->
  Zfa (Zgetbit (p - n) z)
   (get_a (Zabstract_fn_rev n p z a b c d e f x))
   (get_b (Zabstract_fn_rev n p z a b c d e f x))
   (get_c (Zabstract_fn_rev n p z a b c d e f x))
   (get_d (Zabstract_fn_rev n p z a b c d e f x))
   (get_e (Zabstract_fn_rev n p z a b c d e f x))
   (get_f (Zabstract_fn_rev n p z a b c d e f x))
   x
  =
  get_a (Zabstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite Zabstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (Zabstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma Zabstract_fn_b : forall n p (z a b c d e f x : Z),
  0 <= n ->
  Zfb (Zgetbit (p - n) z)
   (get_a (Zabstract_fn_rev n p z a b c d e f x))
   (get_b (Zabstract_fn_rev n p z a b c d e f x))
   (get_c (Zabstract_fn_rev n p z a b c d e f x))
   (get_d (Zabstract_fn_rev n p z a b c d e f x))
   (get_e (Zabstract_fn_rev n p z a b c d e f x))
   (get_f (Zabstract_fn_rev n p z a b c d e f x))
   x
  =
  get_b (Zabstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite Zabstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (Zabstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma Zabstract_fn_c : forall n p (z a b c d e f x : Z),
  0 <= n ->
  Zfc (Zgetbit (p - n) z)
   (get_a (Zabstract_fn_rev n p z a b c d e f x))
   (get_b (Zabstract_fn_rev n p z a b c d e f x))
   (get_c (Zabstract_fn_rev n p z a b c d e f x))
   (get_d (Zabstract_fn_rev n p z a b c d e f x))
   (get_e (Zabstract_fn_rev n p z a b c d e f x))
   (get_f (Zabstract_fn_rev n p z a b c d e f x))
   x
  =
  get_c (Zabstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite Zabstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (Zabstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma Zabstract_fn_d : forall n p (z a b c d e f x : Z),
  0 <= n ->
  Zfd (Zgetbit (p - n) z)
   (get_a (Zabstract_fn_rev n p z a b c d e f x))
   (get_b (Zabstract_fn_rev n p z a b c d e f x))
   (get_c (Zabstract_fn_rev n p z a b c d e f x))
   (get_d (Zabstract_fn_rev n p z a b c d e f x))
   (get_e (Zabstract_fn_rev n p z a b c d e f x))
   (get_f (Zabstract_fn_rev n p z a b c d e f x))
   x
  =
  get_d (Zabstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite Zabstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (Zabstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma Zabstract_fn_e : forall n p (z a b c d e f x : Z),
  0 <= n ->
  Zfe (Zgetbit (p - n) z)
   (get_a (Zabstract_fn_rev n p z a b c d e f x))
   (get_b (Zabstract_fn_rev n p z a b c d e f x))
   (get_c (Zabstract_fn_rev n p z a b c d e f x))
   (get_d (Zabstract_fn_rev n p z a b c d e f x))
   (get_e (Zabstract_fn_rev n p z a b c d e f x))
   (get_f (Zabstract_fn_rev n p z a b c d e f x))
   x
  =
  get_e (Zabstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite Zabstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (Zabstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.
Lemma Zabstract_fn_f : forall n p (z a b c d e f x : Z),
  0 <= n ->
  Zff (Zgetbit (p - n) z)
   (get_a (Zabstract_fn_rev n p z a b c d e f x))
   (get_b (Zabstract_fn_rev n p z a b c d e f x))
   (get_c (Zabstract_fn_rev n p z a b c d e f x))
   (get_d (Zabstract_fn_rev n p z a b c d e f x))
   (get_e (Zabstract_fn_rev n p z a b c d e f x))
   (get_f (Zabstract_fn_rev n p z a b c d e f x))
   x
  =
  get_f (Zabstract_fn_rev (n + 1) p z a b c d e f x).
Proof.
intros. symmetry; rewrite Zabstract_fn_rev_equation. replace (n + 1 - 1) with n by omega.
intros; simpl; destruct (Zabstract_fn_rev n p z a b c d e f x) as (((((a0,b0),c0),d0),e0),f0).
replace (n + 1 <=? 0) with false ; try reflexivity.
symmetry ; apply Z.leb_gt ; omega.
Qed.

Close Scope Z.

End ScalarRec.
