Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Export Mid.SumList.

Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZsumList_correct_impl : forall a b o, a ⊕ b = o -> (ℤ.lst a) + (ℤ.lst b) = ℤ.lst o.
Proof.
  induction a , b.
  - intros o HSum ; go.
  - intros o HSum ; go.
  - intros o HSum ; go.
  - intros o HSum.
    destruct o ; go.
    simpl in HSum.
    assert(Hh:= HSum).
    simplify_list_eq.
    rewrite <- Z.add_shuffle2.
    rewrite Zred_factor4.
    apply Zplus_eq_compat.
    f_equal.
    rewrite Z.add_comm.
    erewrite IHa ; eauto.
Qed.

Corollary ZsumList_correct: forall a b, (ℤ.lst a ⊕ b) = (ℤ.lst a) + (ℤ.lst b).
Proof.
  intros a b.
  assert(exists o, o = a ⊕ b) by (exists (a ⊕ b) ; go) ; destruct H.
  symmetry; subst x ; apply ZsumList_correct_impl ; go.
Qed.

Lemma ZsumList_bound_lt: forall m1 n1 m2 n2 a b, 
  (fun x => m1 < x < n1) 0 ->
  (fun x => m2 < x < n2) 0 ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (a ⊕ b).
Proof.
  introv Hmn1 Hmn2 Ha Hb.
  rewrite ZsumList_Zipp_eq.
  eapply (Forall_Zipp_0 _ (fun x : ℤ => m1 < x < n1) (fun x : ℤ => m2 < x < n2)) ; go.
Qed.

Lemma ZsumList_bound_le: forall m1 n1 m2 n2 a b, 
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (a ⊕ b).
Proof.
  introv Hmn1 Hmn2 Ha Hb.
  rewrite ZsumList_Zipp_eq.
  eapply (Forall_Zipp_0 _ (fun x : ℤ => m1 <= x <= n1) (fun x : ℤ => m2 <= x <= n2)) ; go.
Qed.

Lemma ZsumList_bound_lenght_lt: forall m1 n1 m2 n2 a b, 
  length a = length b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (a ⊕ b).
Proof.
  introv Hl Ha Hb.
  rewrite ZsumList_Zipp_eq.
  eapply (Forall_Zipp_length _ (fun x : ℤ => m1 < x < n1) (fun x : ℤ => m2 < x < n2)) ; go.
Qed.

Lemma ZsumList_bound_Zlength_lt: forall m1 n1 m2 n2 a b, 
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (a ⊕ b).
Proof. convert_length_to_Zlength ZsumList_bound_lenght_lt. Qed.

Lemma ZsumList_bound_length_le: forall m1 n1 m2 n2 a b, 
  length a = length b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (a ⊕ b).
Proof.
  introv Hl Ha Hb.
  rewrite ZsumList_Zipp_eq.
  eapply (Forall_Zipp_length _ (fun x : ℤ => m1 <= x <= n1) (fun x : ℤ => m2 <= x <= n2)) ; go.
Qed.

Lemma ZsumList_bound_Zlength_le: forall m1 n1 m2 n2 a b, 
  Zlength a = Zlength b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (a ⊕ b).
Proof. convert_length_to_Zlength ZsumList_bound_length_le. Qed.

End Integer.

Close Scope Z.

Module Low.

Definition A a b := ZsumList a b.

End Low.

Lemma A_length : forall a b,
  length a = 16 ->
  length b = 16 ->
  length (Low.A a b) = 16.
Proof. intros; rewrite ZsumList_length_max H H0 //. Qed.

Open Scope Z.

Lemma A_correct: forall n a b, ZofList n (Low.A a b) = (ZofList n a) + (ZofList n b).
Proof.
  intros n a b.
  rewrite /A.
  apply ZsumList_correct.
Qed.

Lemma A_Zlength : forall a b,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength (Low.A a b) = 16.
Proof. intros; rewrite ZsumList_Zlength_max H H0 //. Qed.

Lemma A_bound_length_le : forall m1 n1 m2 n2 a b,
  length a = length b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (Low.A a b).
Proof. intros; apply ZsumList_bound_length_le ; auto. Qed.

Lemma A_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (Low.A a b).
Proof. intros; apply ZsumList_bound_Zlength_le ; auto. Qed.

Lemma A_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (Low.A a b).
Proof. intros; apply ZsumList_bound_Zlength_lt ; auto. Qed.

Close Scope Z.