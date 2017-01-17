Require Import Libs.Export.
Require Export ListsOp.ZbinopList.
Require Export ListsOp.ZunopList.

Lemma Forall_ZbinopList_len: forall (f:Z -> Z -> Z) (P Q R: Z -> Prop) (a b: list Z),
  (forall x y, P x -> Q y -> R (f x y)) ->
  length a = length b -> 
  Forall P a -> 
  Forall Q b -> 
  Forall R (ZbinopList f a b).
Proof.
  intros f P Q R.
  induction a ; intros b Hf Hl Ha Hb.
  - simpl in Hl; symmetry in Hl; rewrite length_zero_iff_nil in Hl.
    subst b ; go.
  - destruct b ; inv Hl.
    simpl.
    inv Ha.
    inv Hb.
    apply Forall_cons.
    apply Hf ; go.
    apply IHa ; go.
Qed.

Lemma Forall_ZbinopList_0: forall (f:Z -> Z -> Z) (P Q R: Z -> Prop) (a b: list Z),
  (forall x y, P x -> Q y -> R (f x y)) ->
  P 0%Z ->
  Q 0%Z ->
  Forall P a -> 
  Forall Q b -> 
  Forall R (ZbinopList f a b).
Proof.
  intros f P Q R.
  induction a ; intros b Hf HP HQ Ha Hb.
  - induction b ; go.
    simpl.
    inv Hb.
    apply Forall_cons.
    apply Hf ; go.
    rewrite <- ZbinopList_map_r.
    go.
  - induction b ; inv Ha ; inv Hb ; simpl ; apply Forall_cons.
    apply Hf ; go.
    rewrite <- ZbinopList_map_l ; apply IHa ; go.
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
  apply Forall_cons.
  - apply Hf ; go.
  - apply IHb ; go.
Qed.

