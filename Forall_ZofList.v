Require Export Forall_extended.
Require Export notations.
Require Export ZofList.

Open Scope Z.

Import ListNotations.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

(*
  Forall LEMMAS
*)

Definition ZList_pos (l:list Z) : Prop := Forall (Zle 0) l.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZofList_pos : forall l, ZList_pos l -> 0 <= ℤ.lst l.
Proof.
  intros l Hl.
  dependent induction Hl.
  - go.
  - rewrite ZofList_cons.
    apply OMEGA2.
    assumption.
    rewrite Z.mul_comm.
    apply Zmult_gt_0_le_0_compat.
    apply pown0.
    auto.
    auto.
Qed.

Lemma ZofList_null : forall l, ZList_pos l -> ℤ.lst l = 0 -> Forall (Z.eq 0) l.
Proof.
  intros l HFl HSl.
  induction HFl.
  - go.
  - assert(Hx: {x < 0} + {x = 0} + {x > 0}) by apply Ztrichotomy_inf.
    assert(Hl: {ℤ.lst l < 0} + {ℤ.lst l = 0} + {ℤ.lst l > 0}) by apply Ztrichotomy_inf.
    rewrite ZofList_cons in HSl.
    assert(Hlpos:= ZofList_pos l HFl).
    case Hl ; intro Hl'.
    case Hl' ; intro Hl''.
    apply Zle_not_lt in Hlpos.
    false.
    + clear Hl' Hl Hlpos.
      case Hx ; intro Hx'.
      case Hx' ; intro Hx''.
      apply Zle_not_lt in H.
      false.
      * clear Hx' Hx.
      apply Forall_cons ; go.
      * assert(2 ^ n * (ℤ.lst l) = 0).
        rewrite Z.eq_mul_0 ; auto.
        rewrite H0 in HSl.
        omega. (* contradiction between x = 0 and x > 0*)
    + clear Hlpos Hl.
      case Hx ; intro Hx'.
      case Hx' ; intro Hx''.
      apply Zle_not_lt in H.
      false.
      * clear Hx' Hx.
        subst x ; clear H.
        rewrite Z.add_0_l in HSl.
        rewrite Z.eq_mul_0 in HSl.
        destruct HSl.
          assert(H0' := pown0 n Hn) ; omega.
          omega (* contraction between H and Hl'*).
      * (*once again we need to show a contradiction in HSl. *)
        assert(0 < x + 2 ^ n * (ℤ.lst l)).
          apply Z.add_pos_pos.
          omega. (*see Hx' *)
          rewrite Z.lt_0_mul.
          left ; split ; rewrite <- Z.gt_lt_iff.
          apply pown0 ; auto.
          assumption. (* apply Hl' *)
        omega.
Qed.

Lemma ZofList_bound : forall (m:Z) l , 0 <= m < 2 ^ n -> ZList_pos l -> ℤ.lst l = m -> nth 0 l 0 = m.
Proof.
  intros m l Hm HFl HSlm.
  destruct l.
  - go.
  - rewrite ZofList_cons in HSlm.
    unfold nth.
    subst m.
    replace (2 ^ n * (ℤ.lst l)) with 0.
    apply Zplus_0_r_reverse.
    unfold ZList_pos in HFl.
    rewrite Forall_cons' in HFl.
    destruct HFl as [Hz Hpos].
    apply ZofList_pos in Hpos.
    assert(Hl: {ℤ.lst l < 0} + {ℤ.lst l = 0} + {ℤ.lst l > 0}) by apply Ztrichotomy_inf.
    case Hl ; intro Hl'.
    case Hl' ; intro Hl''.
    apply Zle_not_lt in Hpos.
    false.
    + symmetry. rewrite Z.eq_mul_0 ; auto.
    + exfalso.
      clear Hl Hpos.
      assert(1 <= ℤ.lst l).
      omega.
      assert(2 ^ n * 1 <= 2 ^ n * (ℤ.lst l)).
      apply Zmult_le_compat_l ; auto.
      rewrite <- Z.ge_le_iff.
      assert(Ht:= pown0).
      omega.
      omega.
Qed.

End Integer.