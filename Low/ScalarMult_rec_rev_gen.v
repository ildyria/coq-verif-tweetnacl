(* Require Import ssreflect.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.AMZubSqSel.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Gen.ABCDEF.
Require Import Tweetnacl.Gen.abstract_rec_rev.

Section ScalarRec.

Open Scope Z.

Context {O : Ops (list Z)}.
Context {OP : @Ops_Prop O}.

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

End ScalarRec. *)