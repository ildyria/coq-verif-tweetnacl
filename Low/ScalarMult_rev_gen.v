Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Low.Get_abcdef.

Section ScalarRec.

Variable A : list Z -> list Z -> list Z.
Variable M : list Z -> list Z -> list Z.
Variable Zub : list Z -> list Z -> list Z.
Variable Sq : list Z -> list Z.
Variable _121665: list Z.
Variable Sel25519 : Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Definition fa := fa A M Zub Sq Sel25519.
Definition fb := fb A M Zub Sq Sel25519.
Definition fc := fc A M Zub Sq _121665 Sel25519.
Definition fd := fd A M Zub Sq _121665 Sel25519.
Definition fe := fe A M Zub Sel25519.
Definition ff := ff Zub Sq Sel25519.

(*
Definition step_abstract n z (a b c d e f x:list Z) := let r := getbit (Z.of_nat n) z in
  (fa r a b c d e f x,
  fb r a b c d e f x,
  fc r a b c d e f x,
  fd r a b c d e f x,
  fe r a b c d e f x,
  ff r a b c d e f x).
 *)
Fixpoint abstract_rec_rev m p (z a b c d e f x : list Z) : (list Z * list Z * list Z * list Z * list Z * list Z)
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

Lemma abstract_step_rev_a : forall n p (z a b c d e f x : list Z),
  fa (getbit (Z.of_nat (p - n)) z)
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

Lemma abstract_step_rev_b : forall n p (z a b c d e f x : list Z),
  fb (getbit (Z.of_nat (p - n)) z)
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

Lemma abstract_step_rev_c : forall n p (z a b c d e f x : list Z),
  fc (getbit (Z.of_nat (p - n)) z)
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

Lemma abstract_step_rev_d : forall n p (z a b c d e f x : list Z),
  fd (getbit (Z.of_nat (p - n)) z)
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

Lemma abstract_step_rev_e : forall n p (z a b c d e f x : list Z),
  fe (getbit (Z.of_nat (p - n)) z)
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

Lemma abstract_step_rev_f : forall n p (z a b c d e f x : list Z),
  ff (getbit (Z.of_nat (p - n)) z)
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
(* 
Variable A_length : forall a b, length a = 16 -> length b = 16 -> length (A a b) = 16.
Variable M_length : forall a b, length a = 16 -> length b = 16 -> length (M a b) = 16.
Variable Zub_length : forall a b, length a = 16 -> length b = 16 -> length (Zub a b) = 16.
Variable Sq_length : forall a, length a = 16 -> length (Sq a) = 16.
Variable Sel25519_length : forall b p q, length p = 16 -> length q = 16 -> length (Sel25519 b p q) = 16.
Variable _121665_length : length _121665 = 16.
 *)
Open Scope Z.

Variable A_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (A a b) = 16.
Variable M_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (M a b) = 16.
Variable Zub_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (Zub a b) = 16.
Variable Sq_Zlength : forall a, Zlength a = 16 -> Zlength (Sq a) = 16.
Variable Sel25519_Zlength : forall b p q, Zlength p = 16 -> Zlength q = 16 -> Zlength (Sel25519 b p q) = 16.
Variable _121665_Zlength : Zlength _121665 = 16.

Close Scope Z.

Local Ltac solve_dependencies_length :=
  intros;
  repeat match goal with
    | _ => omega
(*     | _ => apply Sel25519_length *)
(*     | _ => apply M_length *)
(*     | _ => apply Sq_length *)
(*     | _ => apply A_length *)
(*     | _ => apply Zub_length *)
    | _ => apply Sel25519_Zlength
    | _ => apply M_Zlength
    | _ => apply Sq_Zlength
    | _ => apply A_Zlength
    | _ => apply Zub_Zlength
  end ; reflexivity.

(* Lemma fa_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fa r a b c d e f x) = 16.
Proof. apply (fa_length _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fb_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fb r a b c d e f x) = 16.
Proof. apply (fb_length _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fc_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fc r a b c d e f x) = 16.
Proof. apply (fc_length _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fd_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fd r a b c d e f x) = 16.
Proof. apply (fd_length _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fe_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fe r a b c d e f x) = 16.
Proof. apply (fe_length _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma ff_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (ff r a b c d e f x) = 16.
Proof. apply (ff_length _ _ _121665) ; solve_dependencies_length. Qed.
 *)
Open Scope Z.

Lemma fa_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fa r a b c d e f x) = 16.
Proof. apply (fa_Zlength _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fb_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fb r a b c d e f x) = 16.
Proof. apply (fb_Zlength _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fc_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fc r a b c d e f x) = 16.
Proof. apply (fc_Zlength _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fd_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fd r a b c d e f x) = 16.
Proof. apply (fd_Zlength _ _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma fe_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fe r a b c d e f x) = 16.
Proof. apply (fe_Zlength _ _ _ _121665) ; solve_dependencies_length. Qed.
Lemma ff_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (ff r a b c d e f x) = 16.
Proof. apply (ff_Zlength _ _ _121665) ; solve_dependencies_length. Qed.

Close Scope Z.

(* Lemma abstract_rec_length : forall n p z a b c d e f x a' b' c' d' e' f',
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x) -> 
  length a' = 16 
  /\ length b' = 16
   /\ length c' = 16
    /\ length d' = 16
     /\ length e' = 16
      /\ length f' = 16.
Proof. induction n ; intros. go.
simpl in H6.
remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
inversion H6.
assert(Ht:= IHn p z a b c d e f x a0 b0 c0 d0 e0 f0 H H0 H1 H2 H3 H4 H5 Heqk).
jauto_set.
apply fa_length ; auto.
apply fb_length ; auto.
apply fc_length ; auto.
apply fd_length ; auto.
apply fe_length ; auto.
apply ff_length ; auto.
Qed.

Lemma get_a_abstract_rec_length : forall n p z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_a (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_length n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_b_abstract_rec_length : forall n p z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_b (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_length n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_c_abstract_rec_length : forall n p z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_c (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_length n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_d_abstract_rec_length : forall n p z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_d (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_length n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_e_abstract_rec_length : forall n p z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_e (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_length n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_f_abstract_rec_length : forall n p z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_f (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_length n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed. *)

Open Scope Z.

Lemma abstract_rec_Zlength : forall n p z a b c d e f x a' b' c' d' e' f',
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x) -> 
  Zlength a' = 16 
  /\ Zlength b' = 16
   /\ Zlength c' = 16
    /\ Zlength d' = 16
     /\ Zlength e' = 16
      /\ Zlength f' = 16.
Proof. induction n ; intros. go.
simpl in H6.
remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
inversion H6.
assert(Ht:= IHn p z a b c d e f x a0 b0 c0 d0 e0 f0 H H0 H1 H2 H3 H4 H5 Heqk).
jauto_set.
apply fa_Zlength ; auto.
apply fb_Zlength ; auto.
apply fc_Zlength ; auto.
apply fd_Zlength ; auto.
apply fe_Zlength ; auto.
apply ff_Zlength ; auto.
Qed.

Lemma get_a_abstract_rec_Zlength : forall n p z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_a (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_b_abstract_rec_Zlength : forall n p z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_b (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_c_abstract_rec_Zlength : forall n p z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_c (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_d_abstract_rec_Zlength : forall n p z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_d (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_e_abstract_rec_Zlength : forall n p z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_e (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_f_abstract_rec_Zlength : forall n p z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_f (abstract_rec_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 He).
rewrite -He; jauto_set; go.
Qed.

Variable M_bound_Zlength : forall a b,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Variable Sq_bound_Zlength : forall a,
  Zlength a = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Sq a).
Variable A_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (A a b).
Variable A_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (A a b).
Variable Zub_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 - n2 <= x <= n1 - m2) (Zub a b).
Variable Zub_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 - n2 < x < n1 - m2) (Zub a b).
Variable Sel25519_bound_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin <= x <= pmax) p ->
  Forall (fun x => qmin <= x <= qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q).
(*
Variable Sel25519_bound_lt_trans_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q).
*)
(*
Variable Sel25519_bound_lt : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin < x < Z.max pmax qmax) (Sel25519 b p q).
*)
Variable Sel25519_bound_lt_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x < pmax) p ->
  Forall (fun x => pmin <= x < pmax) q -> forall b,
  Forall (fun x => pmin <= x < pmax) (Sel25519 b p q).
Variable Sel25519_bound_lt_lt_id : forall pmin pmax p q,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => pmin < x < pmax) q -> forall b,
  Forall (fun x => pmin < x < pmax) (Sel25519 b p q).
(*
Variable Sel25519_bound_le_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x <= pmax) p ->
  Forall (fun x => pmin <= x <= pmax) q -> forall b,
  Forall (fun x => pmin <= x <= pmax) (Sel25519 b p q).
*)
Variable Sel25519_bound_le_lt_trans_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x < pmax) p ->
  Forall (fun x => pmin <= x < pmax) q -> forall b,
  Forall (fun x => pmin <= x <= pmax) (Sel25519 b p q).
Variable _121665_bound : Forall (fun x => 0 <= x < 2 ^16) _121665.

Local Ltac solve_fx_bound := 
match goal with
  | _ => solve_dependencies_length
  | _ => apply M_bound_Zlength
  | _ => apply Sq_bound_Zlength
  | _ => apply A_bound_Zlength_le
  | _ => apply A_bound_Zlength_lt
  | _ => apply Zub_bound_Zlength_lt
  | _ => apply Sel25519_bound_lt_le_id ; assumption
  | _ => apply Sel25519_bound_lt_lt_id ; assumption
  | _ => apply Sel25519_bound_le_lt_trans_le_id ; assumption
  | _ => apply _121665_bound
end.

Lemma fa_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fa r a b c d e f x).
Proof. apply (fa_bound _ _ _ _ _121665) ; solve_fx_bound. Qed.
Lemma fb_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fb r a b c d e f x).
Proof. apply (fb_bound _ _ _ _ _121665) ; solve_fx_bound. Qed.
Lemma fc_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fc r a b c d e f x).
Proof. apply (fc_bound _ _ _ _ _121665) ; solve_fx_bound. Qed.
Lemma fd_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fd r a b c d e f x).
Proof. apply (fd_bound _ _ _ _ _121665) ; solve_fx_bound. Qed.

Lemma abstract_rec_rev_bound : forall n p z a b c d e f x a' b' c' d' e' f',
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x) -> 
    Forall (fun x => -38 <= x < 2^16 + 38) a'
    /\ Forall (fun x => -38 <= x < 2^16 + 38) b'
    /\ Forall (fun x => -38 <= x < 2^16 + 38) c'
    /\ Forall (fun x => -38 <= x < 2^16 + 38) d'.
Proof. induction n ; intros. go.
simpl in H11.
remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
inversion H11.
assert(Ht:= IHn p z a b c d e f x a0 b0 c0 d0 e0 f0 H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Heqk) ; auto.
assert(Htt := abstract_rec_Zlength n p z a b c d e f x a0 b0 c0 d0 e0 f0 H H0 H1 H2 H3 H4 H5 Heqk).
jauto_set.
apply fa_bound ; go.
apply fb_bound ; go.
apply fc_bound ; go.
apply fd_bound ; go.
Qed.

Lemma get_a_abstract_rec_rev_bound : forall n p z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_b_abstract_rec_rev_bound : forall n p z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_c_abstract_rec_rev_bound : forall n p z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_d_abstract_rec_rev_bound : forall n p z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 He).
rewrite -He; jauto_set; go.
Qed.

(* Ltac solve_montgomery_op_Zlength :=
  repeat match goal with
    | _ => omega
    | _ => rewrite Zlength_map
    | _ => rewrite Sel25519_Zlength
    | _ => rewrite M_Zlength
    | _ => rewrite Sq_Zlength
    | _ => rewrite A_Zlength
    | _ => rewrite Zub_Zlength
    | _ => rewrite get_a_montgomery_step_Zlength
    | _ => rewrite get_b_montgomery_step_Zlength
    | _ => rewrite get_c_montgomery_step_Zlength
    | _ => rewrite get_d_montgomery_step_Zlength
    | _ => rewrite get_e_montgomery_step_Zlength
    | _ => rewrite get_f_montgomery_step_Zlength
    | _ => rewrite get_a_montgomery_rec_Zlength
    | _ => rewrite get_b_montgomery_rec_Zlength
    | _ => rewrite get_c_montgomery_rec_Zlength
    | _ => rewrite get_d_montgomery_rec_Zlength
    | _ => rewrite get_e_montgomery_rec_Zlength
    | _ => rewrite get_f_montgomery_rec_Zlength
  end ; reflexivity.
 *)

Require Recdef.
Function abstract_fn_rev (m p:Z) (z a b c d e f x : list Z) {measure Z.to_nat m} : (list Z * list Z * list Z * list Z * list Z * list Z) :=
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

Lemma abstract_fn_rev_eq : forall m p z a b c d e f x,
  0 <= m ->
  0 <= p ->
  m <= p ->
  abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = 
  abstract_fn_rev m p z a b c d e f x.
Proof.
  clear A_Zlength M_Zlength Zub_Zlength Sq_Zlength Sel25519_Zlength.
  clear M_bound_Zlength Sq_bound_Zlength A_bound_Zlength_le A_bound_Zlength_lt.
  clear Zub_bound_Zlength_le Zub_bound_Zlength_lt Sel25519_bound_le Sel25519_bound_lt_le_id.
  clear Sel25519_bound_lt_lt_id Sel25519_bound_le_lt_trans_le_id _121665_bound _121665_Zlength.
  intros m p z a b c d e f x Hm.
  gen p z a b c d e f x.
  gen m.
  apply (natlike_ind (fun m => forall (p : ℤ) (z a b c d e f x : list ℤ),
0 <= p -> m <= p -> abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = abstract_fn_rev m p z a b c d e f x)).
  - intros; rewrite abstract_fn_rev_equation Zle_imp_le_bool ; try omega ; reflexivity.
  - intros m Hm IHm p z a b c d e f x Hp Hmpp.
    sort. (* sort the hypothesises *)
  assert(Hmp: m <= p) by omega.
  change (Z.succ m) with (m + 1).
  replace (Z.to_nat (m + 1)) with (S (Z.to_nat m)).
  2:   rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite abstract_fn_rev_equation; simpl.
  remember (abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  replace (m + 1 - 1) with m by omega.
  remember (abstract_fn_rev m p z a b c d e f x) as k' ; destruct k' as (((((a0',b0'),c0'),d0'),e0'),f0').
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  assert((a0, b0, c0, d0, e0, f0) = (a0', b0', c0', d0', e0', f0')).
  rewrite Heqk' Heqk.
  apply IHm ; omega.
  inversion H ; subst.
  do 7 f_equal ; rewrite -Z2Nat.inj_sub ; try omega ; apply Z2Nat.id; omega.
Qed.



























End ScalarRec.
