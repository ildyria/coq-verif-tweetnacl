Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_step_gen.

Section ScalarRec.

Variable fa : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fb : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fc : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fd : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fe : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable ff : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

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


(* Proof of the Currying of the function  *)
Definition step_gen :=  step_gen fa fb fc fd fe ff getbit.

Arguments rec_fn_rev_acc [T] _ _ _.
Arguments rec_fn_rev [T] _ _.

Definition abstract_rec_fn (z x:list Z) (n:nat) (a b c d e f : list Z) := rec_fn_rev (step_gen z x) n (a,b,c,d,e,f).

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

Open Scope Z.

Variable fa_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fa r a b c d e f x) = 16.
Variable fb_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fb r a b c d e f x) = 16.
Variable fc_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fc r a b c d e f x) = 16.
Variable fd_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fd r a b c d e f x) = 16.
Variable fe_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fe r a b c d e f x) = 16.
Variable ff_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (ff r a b c d e f x) = 16.

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

Variable fa_bound : forall r a b c d e f x,
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
Variable fb_bound : forall r a b c d e f x,
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
Variable fc_bound : forall r a b c d e f x,
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
Variable fd_bound : forall r a b c d e f x,
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

Close Scope Z.

End ScalarRec.