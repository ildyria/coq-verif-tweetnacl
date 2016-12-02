Require Export SumList.
Require Export Forall_ZofList.
Require Export Forall_ZopList.
Import ListNotations.

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
    apply headSame in Hh.
    apply tailSame in HSum.
    apply IHa in HSum.
    unfold ZofList.
    rewrite <- Z.add_shuffle2.
    rewrite Zred_factor4.
    apply Zplus_eq_compat.
    apply Hh.
    f_equal.
    rewrite Z.add_comm.
    apply HSum.
Qed.

Corollary ZsumList_correct: forall a b, (ℤ.lst a ⊕ b) = (ℤ.lst a) + (ℤ.lst b).
Proof.
  intros a b.
  assert(exists o, o = a ⊕ b) by (exists (a ⊕ b) ; go) ; destruct H.
  symmetry; subst x ; apply ZsumList_correct_impl ; go.
Qed.

Lemma ZsumList_bound: forall m1 n1 m2 n2 a b, 
  length a = length b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (a ⊕ b).
Proof.
  introv Hl Ha Hb.
  rewrite ZsumList_ZbinopList_eq.
  eapply (Forall_ZbinopList _ (fun x : ℤ => m1 < x < n1) (fun x : ℤ => m2 < x < n2)) ; go.
Qed.
(*
Lemma ZsumList_pos: forall a b, ZList_pos a -> ZList_pos b -> ZList_pos (a ⊕ b).
Proof.
  induction a , b ; intros.
  - auto.
  - auto.
  - auto.
  - simpl.
    unfold ZList_pos in *.
    rewrite Forall_cons'.
    rewrite Forall_cons' in H.
    rewrite Forall_cons' in H0.
    destruct H, H0. go.
Qed.
*)
End Integer.
