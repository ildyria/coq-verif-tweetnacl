Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind".

Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Gen.AMZubSqSel_List.
Require Import Tweetnacl.Gen.ABCDEF.
Require Import Tweetnacl.Gen.abstract_fn_rev.
Section ScalarRec.

Open Scope Z.

Context {O : Ops (list Z) (list Z) id}.
Context {OP : @Ops_List O}.

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

Lemma abstract_fn_rev_bound : forall n p z a b c d e f x a' b' c' d' e' f',
  0 <= n ->
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
Proof. intros m p z a b c d e f x a' b' c' d' e' f' Hm.
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
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) a ->
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) b ->
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) c ->
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) d ->
Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
(a', b', c', d', e', f') = abstract_fn_rev m p z a b c d e f x ->
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) a' /\
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) b' /\
Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) c' /\ Forall (fun x0 : ℤ => -38 <= x0 < 2 ^ 16 + 38) d')).
move=> p z a b c d e f x a' b' c' d' e' f' (* Hn Hp Hnp*) Ha Hb Hc Hd He Hf Hx 
Haa Hbb Hcc Hdd Hxx.
rewrite abstract_fn_rev_0 => Hh.
inv Hh ; go.
move => m Hm IHm p z a b c d e f x a' b' c' d' e' f' (* Hn Hp Hnp*) Ha Hb Hc Hd He Hf Hx 
Haa Hbb Hcc Hdd Hxx.
rewrite abstract_fn_rev_n. 2: omega.
replace (Z.succ m - 1) with m.
2: omega.
remember (abstract_fn_rev m p z a b c d e f x) as k.
destruct k as (((((a0,b0),c0),d0),e0),f0).
remember (Getbit (p - m) z) as r.
simpl => Hh.
inv Hh.
assert(Ht:= IHm p z a b c d e f x a0 b0 c0 d0 e0 f0 Ha Hb Hc Hd He Hf Hx Haa Hbb Hcc Hdd Hxx Heqk) ; auto.
assert(Htt := abstract_fn_Zlength m p z a b c d e f x a0 b0 c0 d0 e0 f0 Hm Ha Hb Hc Hd He Hf Hx Heqk).
jauto_set.
apply fa_bound ; go.
apply fb_bound ; go.
apply fc_bound ; go.
apply fd_bound ; go.
Qed.


Lemma get_a_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
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
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_b_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
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
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_c_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
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
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 He).
rewrite -He; jauto_set; go.
Qed.
Lemma get_d_abstract_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
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
assert(Ht := abstract_fn_rev_bound n p z a b c d e f x a' b' c' d' e' f' H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 He).
rewrite -He; jauto_set; go.
Qed.

Close Scope Z.

End ScalarRec.
