Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.

Require Export Tweetnacl.Op.SubList.
Require Import Tweetnacl.Op.MinusList.
Require Import stdpp.prelude.

Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZsumList_correct_impl : forall a b o, a ⊖ b = o -> (ℤ.lst a) - (ℤ.lst b) = ℤ.lst o.
Proof.
  induction a , b.
  - intros o HSub ; go.
  - intros o HSub; destruct o ; go.
    simpl in *.
    replace (- (z + 2 ^ n * (ℤ.lst b))) with (- z + (- (2 ^ n * (ℤ.lst b)))) by omega.
    apply ListSame in HSub ; destruct HSub. subst.
    rewrite ZminusList_ZofList.
    lia.
  - intros o HSub ; rewrite ZsubList_nil_r in HSub ; subst ; go.
  - intros o HSub.
    destruct o ; go.
    simpl in HSub.
    assert(Hh:= HSub).
    simpl.
    apply ListSame in Hh; destruct Hh as [H0 H1].
    apply IHa in H1.
    rewrite <- H1.
    lia.
Qed.

Corollary ZsumList_correct: forall a b, (ℤ.lst a ⊖ b) = (ℤ.lst a) - (ℤ.lst b).
Proof.
  intros a b.
  assert(exists o, o = a ⊖ b) by (exists (a ⊖ b) ; go) ; destruct H.
  symmetry; subst x ; apply ZsumList_correct_impl ; go.
Qed.

Lemma ZsumList_bound_lt: forall m1 n1 m2 n2 a b, 
  (fun x => m1 < x < n1) 0 ->
  (fun x => m2 < x < n2) 0 ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 - n2 < x < n1 - m2) (a ⊖ b).
Proof.
  introv Hmn1 Hmn2 Ha Hb.
  rewrite ZsubList_Zipp_eq.
  eapply (Forall_Zipp_0 _ (fun x : ℤ => m1 < x < n1) (fun x : ℤ => m2 < x < n2)) ; go.
Qed.

Lemma ZsumList_bound_le: forall m1 n1 m2 n2 a b, 
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 - n2 <= x <= n1 - m2) (a ⊖ b).
Proof.
  introv Hmn1 Hmn2 Ha Hb.
  rewrite ZsubList_Zipp_eq.
  eapply (Forall_Zipp_0 _ (fun x : ℤ => m1 <= x <= n1) (fun x : ℤ => m2 <= x <= n2)) ; go.
Qed.

Lemma ZsumList_bound_lenght_lt: forall m1 n1 m2 n2 a b, 
  length a = length b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 - n2 < x < n1 - m2) (a ⊖ b).
Proof.
  introv Hl Ha Hb.
  rewrite ZsubList_Zipp_eq.
  eapply (Forall_Zipp_length _ (fun x : ℤ => m1 < x < n1) (fun x : ℤ => m2 < x < n2)) ; go.
Qed.

Lemma ZsumList_bound_Zlength_lt: forall m1 n1 m2 n2 a b, 
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 - n2 < x < n1 - m2) (a ⊖ b).
Proof. convert_length_to_Zlength ZsumList_bound_lenght_lt. Qed.

Lemma ZsumList_bound_length_le: forall m1 n1 m2 n2 a b, 
  length a = length b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 - n2 <= x <= n1 - m2) (a ⊖ b).
Proof.
  introv Hl Ha Hb.
  rewrite ZsubList_Zipp_eq.
  eapply (Forall_Zipp_length _ (fun x : ℤ => m1 <= x <= n1) (fun x : ℤ => m2 <= x <= n2)) ; go.
Qed.

Lemma ZsumList_bound_Zlength_le: forall m1 n1 m2 n2 a b, 
  length a = length b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 - n2 <= x <= n1 - m2) (a ⊖ b).
Proof. convert_length_to_Zlength ZsumList_bound_length_le. Qed.

End Integer.

Close Scope Z.