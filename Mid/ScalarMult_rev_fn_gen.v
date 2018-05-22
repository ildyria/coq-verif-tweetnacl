Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind".

Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Recdef.

Section ScalarRec.

Open Scope Z.

Variable fa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable ff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable getbit : Z -> Z -> Z.

Function abstract_fn_rev (m p:Z) (z a b c d e f x : Z) {measure Z.to_nat m} : (Z * Z * Z * Z * Z * Z) :=
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

Lemma abstract_fn_a : forall n p (z a b c d e f x : Z),
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
Lemma abstract_fn_b : forall n p (z a b c d e f x : Z),
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
Lemma abstract_fn_c : forall n p (z a b c d e f x : Z),
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
Lemma abstract_fn_d : forall n p (z a b c d e f x : Z),
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
Lemma abstract_fn_e : forall n p (z a b c d e f x : Z),
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
Lemma abstract_fn_f : forall n p (z a b c d e f x : Z),
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
(* 
Variable fa_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => -38 <= x < 2^16 + 38) (fa r a b c d e f x).
Variable fb_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => -38 <= x < 2^16 + 38) (fb r a b c d e f x).
Variable fc_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
    (fun x => -38 <= x < 2^16 + 38) (fc r a b c d e f x).
Variable fd_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
    (fun x => -38 <= x < 2^16 + 38) (fd r a b c d e f x).

Lemma abstract_fn_rev_bound : forall n p z a b c d e f x a' b' c' d' e' f',
  0 <= n ->
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x) -> 
    (fun x => -38 <= x < 2^16 + 38) a'
    /\ (fun x => -38 <= x < 2^16 + 38) b'
    /\ (fun x => -38 <= x < 2^16 + 38) c'
    /\ (fun x => -38 <= x < 2^16 + 38) d'.
Proof. intros m p z a b c d e f x a' b' c' d' e' f' Hm.
  gen a' b' c' d' e' f'.
  gen p z a b c d e f x.
  gen m.
  apply (natlike_ind (fun m => forall (p : ℤ) (z a b c d e f x a' b' c' d' e' f' : ℤ),
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) a ->
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) b ->
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) c ->
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) d ->
(fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
(a', b', c', d', e', f') = abstract_fn_rev m p z a b c d e f x ->
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) a' /\
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) b' /\
(fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) c' /\ (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) d')).
move=> p z a b c d e f x a' b' c' d' e' f'
Haa Hbb Hcc Hdd Hxx.
rewrite abstract_fn_rev_0 => Hh.
inv Hh ; go.
move => m Hm IHm p z a b c d e f x a' b' c' d' e' f'
Haa Hbb Hcc Hdd Hxx.
rewrite abstract_fn_rev_n. 2: omega.
replace (Z.succ m - 1) with m.
2: omega.
remember (abstract_fn_rev m p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
remember (getbit (p - m) z) as r.
simpl => Hh.
inv Hh.
assert(Ht:= IHm p z a b c d e f x a0 b0 c0 d0 e0 f0 Haa Hbb Hcc Hdd Hxx Heqk) ; auto.
jauto_set ; first [ apply fa_bound | apply fb_bound | apply fc_bound | apply fd_bound ] ; go.
Qed.


Lemma get_a_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_a (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4  He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_b_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_b (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_c_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_c (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_d_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_d (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 He).
rewrite -He; jauto_set; go.
Qed. *)

Close Scope Z.

End ScalarRec.
