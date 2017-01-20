Require Import Prelude.prelude.prelude.
Require Export Tweetnacl.ListsOp.Zipp.
Require Export Tweetnacl.ListsOp.ZunopList.
Require Import Tweetnacl.Libs.Export.

Lemma Forall_Zipp_length: forall (f:Z -> Z -> Z) (P Q R: Z -> Prop) (a b: list Z),
  (forall x y, P x -> Q y -> R (f x y)) ->
  length a = length b -> 
  Forall P a -> 
  Forall Q b -> 
  Forall R (Zipp f a b).
Proof.
  intros f P Q R.
  induction a ; intros b Hf Hl Ha Hb.
  - simpl in Hl; symmetry in Hl; rewrite length_zero_iff_nil in Hl.
    subst b ; go.
  - destruct b ; inv Hl.
    simpl.
    inv Ha.
    inv Hb.
    apply Forall_cons_2.
    apply Hf ; go.
    apply IHa ; go.
Qed.

Lemma Forall_Zipp_Zlenth: forall (f:Z -> Z -> Z) (P Q R: Z -> Prop) (a b: list Z),
  (forall x y, P x -> Q y -> R (f x y)) ->
  Zlength a = Zlength b -> 
  Forall P a -> 
  Forall Q b -> 
  Forall R (Zipp f a b).
Proof.
  intros f P Q R a b Hf Hl Ha Hb.
  repeat rewrite Zlength_correct in Hl.
  eapply Forall_Zipp_length ; eauto ; omega.
Qed.

Lemma Forall_Zipp_0: forall (f:Z -> Z -> Z) (P Q R: Z -> Prop) (a b: list Z),
  (forall x y, P x -> Q y -> R (f x y)) ->
  P 0%Z ->
  Q 0%Z ->
  Forall P a -> 
  Forall Q b -> 
  Forall R (Zipp f a b).
Proof.
  intros f P Q R.
  induction a ; intros b Hf HP HQ Ha Hb.
  - induction b ; go.
    simpl.
    inv Hb.
    apply Forall_cons_2.
    apply Hf ; go.
    rewrite <- Zipp_map_r.
    go.
  - induction b ; inv Ha ; inv Hb ; simpl ; apply Forall_cons_2.
    apply Hf ; go.
    rewrite <- Zipp_map_l ; apply IHa ; go.
    apply Hf ; go.
    apply IHa ; go.
Qed.

Lemma Forall_ZunopList: forall (f:Z -> Z -> Z) (P Q R: Z -> Prop) (a : Z) (b: list Z),
  (forall x y, P x -> Q y -> R (f x y)) ->
  P a -> 
  Forall Q b -> 
  Forall R (ZunopList f a b).
Proof.
  intros f P Q R.
  induction b ; intros Hf Ha Hb ; go.
  inv Hb.
  simpl.
  apply Forall_cons_2.
  - apply Hf ; go.
  - apply IHb ; go.
Qed.
