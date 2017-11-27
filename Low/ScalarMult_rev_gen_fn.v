Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Low.ScalarMult_rev_gen.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Recdef.

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

Definition abstract_rec_rev := abstract_rec_rev A M Zub Sq _121665 Sel25519 getbit.

Open Scope Z.

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
  m <= p + 1 ->
  abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = 
  abstract_fn_rev m p z a b c d e f x.
Proof.
  intros m p z a b c d e f x Hm.
  gen p z a b c d e f x.
  gen m.
  apply (natlike_ind (fun m => forall (p : ℤ) (z a b c d e f x : list ℤ),
0 <= p -> m <= p + 1  -> abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = abstract_fn_rev m p z a b c d e f x)).
  - intros; rewrite abstract_fn_rev_equation Zle_imp_le_bool ; try omega ; reflexivity.
  - intros m Hm IHm p z a b c d e f x Hp Hmpp.
    sort. (* sort the hypothesises *)
  assert(Hmp: m <= p + 1) by omega.
  change (Z.succ m) with (m + 1).
  replace (Z.to_nat (m + 1)) with (S (Z.to_nat m)).
  2:   rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite abstract_fn_rev_equation. simpl.
  fold fa fb fc fd fe ff.
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

Lemma abstract_fn_a : forall n p (z a b c d e f x : list Z),
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
Lemma abstract_fn_b : forall n p (z a b c d e f x : list Z),
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
Lemma abstract_fn_c : forall n p (z a b c d e f x : list Z),
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
Lemma abstract_fn_d : forall n p (z a b c d e f x : list Z),
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
Lemma abstract_fn_e : forall n p (z a b c d e f x : list Z),
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
Lemma abstract_fn_f : forall n p (z a b c d e f x : list Z),
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
    | _ => apply Sel25519_Zlength
    | _ => apply M_Zlength
    | _ => apply Sq_Zlength
    | _ => apply A_Zlength
    | _ => apply Zub_Zlength
  end ; reflexivity.

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

Lemma abstract_fn_Zlength : forall m p z a b c d e f x a' b' c' d' e' f',
  0 <= m ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  (a',b',c',d',e',f') = (abstract_fn_rev m p z a b c d e f x) -> 
  Zlength a' = 16 
  /\ Zlength b' = 16
   /\ Zlength c' = 16
    /\ Zlength d' = 16
     /\ Zlength e' = 16
      /\ Zlength f' = 16.
Proof.
  intros m p z a b c d e f x a' b' c' d' e' f' Hm.
  gen a' b' c' d' e' f'.
  gen p z a b c d e f x.
  gen m.
  apply (natlike_ind (fun m => forall (p : ℤ) (z a b c d e f x a' b' c' d' e' f' : list ℤ),
Zlength a = 16 ->
Zlength b = 16 ->
Zlength c = 16 ->
Zlength d = 16 ->
Zlength e = 16 ->
Zlength f = 16 ->
Zlength x = 16 ->
(a', b', c', d', e', f') = abstract_fn_rev m p z a b c d e f x ->
Zlength a' = 16 /\ Zlength b' = 16 /\ Zlength c' = 16 /\ Zlength d' = 16 /\ Zlength e' = 16 /\ Zlength f' = 16)).
move=> p z a b c d e f x a' b' c' d' e' f'.
move=> Ha Hb Hc Hd He Hf Hx.
rewrite abstract_fn_rev_equation Zle_imp_le_bool ; try omega.
go.
move=> m Hm IHm.
move=> p z a b c d e f x a' b' c' d' e' f'.
move=> Ha Hb Hc Hd He Hf Hx.
change (Z.succ m) with (m + 1).
rewrite abstract_fn_rev_equation.
replace (m + 1 - 1) with m by omega.
remember (abstract_fn_rev m p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
replace (m + 1 <=? 0) with false.
2: symmetry ; apply Z.leb_gt ; omega.
move=> Heq;inversion Heq.
assert(Ht:= IHm p z a b c d e f x a0 b0 c0 d0 e0 f0 Ha Hb Hc Hd He Hf Hx Heqk).
jauto_set.
apply fa_Zlength ; auto.
apply fb_Zlength ; auto.
apply fc_Zlength ; auto.
apply fd_Zlength ; auto.
apply fe_Zlength ; auto.
apply ff_Zlength ; auto.
Qed.

Lemma get_a_abstract_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_a (abstract_fn_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_b_abstract_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_b (abstract_fn_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_c_abstract_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_c (abstract_fn_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_d_abstract_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_d (abstract_fn_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_e_abstract_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_e (abstract_fn_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_f_abstract_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_f (abstract_fn_rev n p z a b c d e f x)) = 16.
Proof. intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_Zlength n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 He).
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
Variable Sel25519_bound_lt_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x < pmax) p ->
  Forall (fun x => pmin <= x < pmax) q -> forall b,
  Forall (fun x => pmin <= x < pmax) (Sel25519 b p q).
Variable Sel25519_bound_lt_lt_id : forall pmin pmax p q,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => pmin < x < pmax) q -> forall b,
  Forall (fun x => pmin < x < pmax) (Sel25519 b p q).
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

Lemma abstract_fn_rev_bound : forall n p z a b c d e f x a' b' c' d' e' f',
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x) -> 
    Forall (fun x => -38 <= x < 2^16 + 38) a'
    /\ Forall (fun x => -38 <= x < 2^16 + 38) b'
    /\ Forall (fun x => -38 <= x < 2^16 + 38) c'
    /\ Forall (fun x => -38 <= x < 2^16 + 38) d'.
Proof. move=> n p z a b c d e f x a' b' c' d' e' f' Hn Hp Hnp Ha Hb Hc Hd He Hf Hx 
Haa Hbb Hcc Hdd Hxx.
rewrite -abstract_fn_rev_eq; try omega ; intros.
eapply abstract_rec_rev_bound.
apply A_Zlength.
apply M_Zlength.
apply Zub_Zlength.
apply Sq_Zlength.
apply Sel25519_Zlength.
apply _121665_Zlength.
apply M_bound_Zlength.
apply Sq_bound_Zlength.
apply A_bound_Zlength_le.
apply A_bound_Zlength_lt.
apply Zub_bound_Zlength_le.
apply Zub_bound_Zlength_lt.
apply Sel25519_bound_le.
apply Sel25519_bound_lt_le_id.
apply Sel25519_bound_lt_lt_id.
apply Sel25519_bound_le_lt_trans_le_id.
apply _121665_bound.
apply Ha.
apply Hb.
apply Hc.
apply Hd.
apply He.
apply Hf.
apply Hx.
apply Haa.
apply Hbb.
apply Hcc.
apply Hdd.
apply Hxx.
fold abstract_rec_rev.
erewrite H.
reflexivity.
Qed.

Lemma get_a_abstract_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_b_abstract_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_c_abstract_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_d_abstract_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (abstract_fn_rev n p z a b c d e f x)).
Proof.
intros.
assert(He: exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev n p z a b c d e f x)).
  remember (abstract_fn_rev n p z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  do 6 eexists ; reflexivity.
destruct He as [a' [b' [c' [d' [e' [f' He]]]]]].
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 He).
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

End ScalarRec.
