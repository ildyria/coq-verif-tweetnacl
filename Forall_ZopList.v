Require Export Forall_extended.
Require Export notations.
Require Export OpList.

Lemma Forall_opList: forall (f:Z -> Z -> Z) (P Q: Z -> Prop) (a b: list Z), (forall x y, P x -> P y -> Q (f x y)) -> length a = length b -> Forall P a -> Forall P b -> Forall Q (ZopList f a b).
Proof.
  intros f P Q.
  induction a ; intros b Hf Hl Ha Hb.
  - simpl in Hl.
    symmetry in Hl.
    rewrite <- lengthNil in Hl.
    go.
  - destruct b ; inv Hl.
    simpl.
    inv Ha.
    inv Hb.
    apply Forall_cons.
    apply Hf ; go.
    apply IHa ; go.
Qed.