Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Low.Get_abcdef.

Require Import Tweetnacl.Mid.ScalarMult_step_gen.

Section ScalarRec.

Variable fa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable ff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable getbit : Z -> Z -> Z.

Fixpoint abstract_rec_rev m p (z a b c d e f x : Z) : (Z * Z * Z * Z * Z * Z)
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


(* Proof of the Currying of the function  *)
Definition step_gen :=  step_gen fa fb fc fd fe ff getbit.

Arguments rec_fn_rev_acc [T] _ _ _.
Arguments rec_fn_rev [T] _ _.

Definition abstract_rec_fn (z x:Z) (n:nat) (a b c d e f :Z) := rec_fn_rev (step_gen z x) n (a,b,c,d,e,f).

Lemma abstract_rec_rev_equiv_recfn_p: forall n p z a b c d e f x,
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
  abstract_rec_rev (S n) n z a b c d e f x = abstract_rec_fn z x (S n) a b c d e f.
Proof. intros. rewrite /abstract_rec_fn /rec_fn_rev -abstract_rec_rev_equiv_recfn_p.
replace (S n - 1) with n ; go.
Qed.






Lemma abstract_step_rev_a : forall n p (z a b c d e f x : Z),
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

Lemma abstract_step_rev_b : forall n p (z a b c d e f x : Z),
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

Lemma abstract_step_rev_c : forall n p (z a b c d e f x : Z),
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

Lemma abstract_step_rev_d : forall n p (z a b c d e f x : Z),
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

Lemma abstract_step_rev_e : forall n p (z a b c d e f x : Z),
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

Lemma abstract_step_rev_f : forall n p (z a b c d e f x : Z),
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

Open Scope Z.

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
Lemma abstract_rec_rev_bound : forall n p z a b c d e f x a' b' c' d' e' f',
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x) -> 
    (fun x => -38 <= x < 2^16 + 38) a'
    /\ (fun x => -38 <= x < 2^16 + 38) b'
    /\ (fun x => -38 <= x < 2^16 + 38) c'
    /\ (fun x => -38 <= x < 2^16 + 38) d'.
Proof. induction n ; intros. go.
simpl in H4.
remember (abstract_rec_rev n p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
inversion H4.
assert(Ht:= IHn p z a b c d e f x a0 b0 c0 d0 e0 f0 H H0 H1 H2 H3 Heqk) ; auto.
jauto_set ; first [apply fa_bound | apply fb_bound | apply fc_bound | apply fd_bound] ; go.
Qed.

Lemma get_a_abstract_rec_rev_bound : forall n p z a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_a (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_b_abstract_rec_rev_bound : forall n p z a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_b (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_c_abstract_rec_rev_bound : forall n p z a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_c (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 He).
rewrite -He; jauto_set; go.
Qed.

Lemma get_d_abstract_rec_rev_bound : forall n p z a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (get_d (abstract_rec_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_rec_rev n p z a b c d e f x)).
  remember (abstract_rec_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_rec_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 He).
rewrite -He; jauto_set; go.
Qed.

Close Scope Z.

End ScalarRec.