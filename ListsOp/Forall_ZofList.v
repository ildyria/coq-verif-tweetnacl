Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Export ListsOp.ZofList.
Open Scope Z.

(* Import ListNotations. *)

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
  dependent induction Hl => //=.
  - apply OMEGA2.
    done.
    rewrite Z.mul_comm.
    apply Zmult_gt_0_le_0_compat.
    apply pown0 ; done.
    done.
Qed.

Lemma ZofList_null: forall l, ZList_pos l -> ℤ.lst l = 0 -> Forall (Z.eq 0) l.
Proof.
  move => l HFl HSl.
  induction HFl => //=.
  - assert(Hx: {x < 0} + {x = 0} + {x > 0}) by apply Ztrichotomy_inf.
    assert(Hl: {ℤ.lst l < 0} + {ℤ.lst l = 0} + {ℤ.lst l > 0}) by apply Ztrichotomy_inf.
    rewrite ZofList_cons in HSl.
    assert(Hlpos:= ZofList_pos l HFl).
    case Hl => Hl'.
    case Hl' => Hl''.
    by apply Zle_not_lt in Hlpos.
    + clear Hl' Hl Hlpos.
      case Hx => Hx'.
      case Hx' => Hx''.
      by apply Zle_not_lt in H.
      * clear Hx' Hx.
      apply Forall_cons; go.
      * assert(2 ^ n * (ℤ.lst l) = 0).
        rewrite Z.eq_mul_0 ; auto.
        rewrite H0 in HSl.
        omega. (* contradiction between x = 0 and x > 0*)
    + clear Hlpos Hl.
      case Hx => Hx'.
      case Hx' => Hx''.
      apply Zle_not_lt in H.
      false.
      * clear Hx' Hx.
        subst x ; clear H.
        move: HSl. rewrite Z.add_0_l Z.eq_mul_0 => HSl.
        destruct HSl.
          assert(H0' := pown0 n Hn) ; omega.
          omega (* contraction between H and Hl'*).
      * (*once again we need to show a contradiction in HSl. *)
        assert(0 < x + 2 ^ n * (ℤ.lst l)).
          apply Z.add_pos_pos.
          omega. (*see Hx' *)
          rewrite Z.lt_0_mul.
          left ; split ; rewrite -Z.gt_lt_iff.
          apply pown0 ; auto.
          assumption. (* apply Hl' *)
        omega.
Qed.

Lemma ZofList_bound: forall (m:Z) l , 0 <= m < 2 ^ n -> ZList_pos l -> ℤ.lst l = m -> nth 0 l 0 = m.
Proof.
  intros m [|x l] Hm HFl HSlm.
  - go.
  - rewrite ZofList_cons in HSlm.
    unfold nth.
    subst m.
    replace (2 ^ n * (ℤ.lst l)) with 0.
    apply Zplus_0_r_reverse.
    move: HFl ; unfold ZList_pos.
    rewrite Forall_cons => HSl. destruct HSl as [Hz Hpos].
    apply ZofList_pos in Hpos.
    assert(Hl: {ℤ.lst l < 0} + {ℤ.lst l = 0} + {ℤ.lst l > 0}) by apply Ztrichotomy_inf.
    case Hl => Hl'.
    case Hl' => Hl''.
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

Lemma ZofList_n_nn_bound_length: forall l (m:nat),
  length l = m -> 
  Forall (fun x => 0 <= x < 2^n) l -> 
    ℤ.lst l < 2^(n*ℤ.ℕ m).
Proof.
  induction l using rev_ind => m Hl Hbounds.
  simpl in Hl ; subst m.
  rewrite <- Zmult_0_r_reverse ; go.
  destruct m;
  move : Hl ; rewrite app_length.
  simpl; oreplace (length l + 1)%nat (S (length l))%nat => Hl.
  try congruence.
  move=> Hl.
  rewrite Nat2Z.inj_succ -Zmult_succ_r_reverse ZofList_app'.
  inversion Hl; clear Hl.
  have : length l = m by omega.
  move => ->.
  replace (ℤ.lst [x]) with x by (simpl ZofList ; omega).
  eapply (Z.lt_le_trans _ (2 ^ (n * (ℤ.ℕ m)) + 2 ^ (n * (ℤ.ℕ m)) * x)).
  - apply Zplus_lt_compat_r.
    apply IHl.
    omega.
    move : Hbounds ; rewrite !Forall_forall => Hbounds.
    intros ; apply Hbounds.
    rewrite elem_of_app.
    left ; assumption.
  - clear H0.
    rewrite Zred_factor2.
    eapply (Z.le_trans _ (2 ^ (n * (ℤ.ℕ m)) * (2^n))).
    + apply Zmult_le_compat_l.
      rewrite Z.add_1_l.
      apply Zlt_le_succ.
      apply Forall_app in Hbounds.
      destruct Hbounds as [Hl Hx].
      move : Hx.
      rewrite Forall_forall => Hx.
      destruct (Hx x) ; go.
      apply Z.pow_nonneg ; omega.
    + apply Z.eq_le_incl.
      rewrite Z.pow_add_r ; try omega.
      rewrite Z.mul_comm.
      apply Zmult_gt_0_le_0_compat ; try omega.
      done.
Qed.

Lemma ZofList_n_nn_bound_Zlength: forall l (m:nat),
  Zlength l = m -> 
  Forall (fun x => 0 <= x < 2^n) l -> 
    ℤ.lst l < 2^(n*m).
Proof. convert_length_to_Zlength ZofList_n_nn_bound_length. Qed.

Fixpoint ZofList_Bound (p:nat) (m: Z) : Z := match p with 
| 0%nat => 0
| S p => m + Z.pow 2 n * ZofList_Bound p m
end.

Lemma ZofList_bounds: forall l (m:nat) (a b:Z),
  (length l = m)%nat -> 
  a < 0 < b ->
  Forall (fun x => a < x < b) l -> 
   ZofList_Bound m a <= ℤ.lst l <= ZofList_Bound m b.
Proof.
  elim => [| h q IHl] => m a b Hm Hab Hl //=.
  subst m ; go.
  destruct m.
  inv Hm.
  inversion Hm.
  rewrite H0.
  apply Forall_cons in Hl.
  destruct Hl as [Hh Hl].
  destruct (IHl m a b H0 Hab Hl) as [Hinf Hsup].
  simpl.
  split.
  apply Z.add_le_mono ; try omega.
  apply Zmult_le_compat_l ; try apply Z.pow_nonneg ; omega.
  apply Z.add_le_mono ; try omega.
  apply Zmult_le_compat_l ; try apply Z.pow_nonneg ; omega.
Qed.


Lemma ZofList_bounds_Zlength: forall l (m:nat) (a b:Z),
  Zlength l = m -> 
  a < 0 < b ->
  Forall (fun x => a < x < b) l -> 
   ZofList_Bound m a <= ℤ.lst l <= ZofList_Bound m b.
Proof. convert_length_to_Zlength ZofList_bounds. Qed.

(* the following lemma is useless! *)
(* Lemma ZofList_bounds': forall l (m:nat) a b,
  (length l = m)%nat -> 
  a < 0 < b ->
  Forall (fun x => a < x < b) l -> 
   2 * a * 2^(n*ℤ.ℕ m) < ℤ.lst l < 2 * b * 2^(n*ℤ.ℕ m).
Proof.
  induction l using rev_ind => m a b Hl Hab Hbounds.
  simpl in Hl ; subst m.
  rewrite <- Zmult_0_r_reverse ; go.
  rewrite !Z.pow_0_r ZofList_nil.
  omega.
  destruct m;
  move : Hl; rewrite app_length; simpl length ; 
  oreplace (length l + 1)%nat (S (length l))%nat => Hl;
  try congruence.
  rewrite Nat2Z.inj_succ -Zmult_succ_r_reverse ZofList_app'.
  2: done.
  inversion Hl; clear Hl.
  rewrite H0.
  replace (ℤ.lst [x]) with x by (simpl ZofList ; omega).
  apply Forall_app in Hbounds.
  destruct Hbounds as [Hl Hx].
  destruct (IHl m a b H0 Hab Hl) as [Hinf Hsup].
  inversion Hx ; subst x0 l0; clear H3.
  destruct H2 as [Hxinf Hxsup].
  split.
  - rewrite Z.add_comm.
    eapply (Z.le_lt_trans _ (2 * a * 2 ^ (n * (ℤ.ℕ m)) + 2 ^ (n * (ℤ.ℕ m)) * x))
    ; [| apply Zplus_lt_compat_r ; omega].
    rewrite Z.pow_add_r. 2: omega. 2: go.
    replace (2 * a * 2 ^ (n * (ℤ.ℕ m))) with (2 ^ (n * (ℤ.ℕ m)) * 2 * a) by ring.
    rewrite -!Z.mul_assoc Zred_factor4.
    replace (2 * (a * (2 ^ n * 2 ^ (n * (ℤ.ℕ m))))) with (2 ^ (n * (ℤ.ℕ m)) * (2 * a * 2 ^ n)) by ring.
    apply Zmult_le_compat_l ; [| apply Z.pow_nonneg ; omega].
    apply (Z.le_trans _ (2 * a * 2)) ; try omega.
    rewrite -!Z.mul_assoc.
    apply Zmult_le_compat_l ; try omega.
    apply Z.mul_le_mono_nonpos_l ; try omega.
    apply pown2 ; omega.
  - eapply (Z.lt_le_trans _ (2 * b * 2 ^ (n * (ℤ.ℕ m)) + 2 ^ (n * (ℤ.ℕ m)) * x)).
    apply Zplus_lt_compat_r ; omega.
    rewrite Z.pow_add_r. 2: go. 2: omega.
    replace (2 * b * 2 ^ (n * (ℤ.ℕ m))) with (2 ^ (n * (ℤ.ℕ m)) * 2 * b) by ring.
    rewrite -!Z.mul_assoc Zred_factor4.
    replace (2 * (b * (2 ^ (n * (ℤ.ℕ m))* 2 ^ n))) with (2 ^ (n * (ℤ.ℕ m)) * (2 * b * 2 ^ n)) by ring.
    apply Zmult_le_compat_l ; [|apply Z.pow_nonneg ; omega].
    apply (Z.le_trans _ (2 * b * 2)) ; try omega.
    apply Zmult_le_compat_l ; try omega.
    apply pown2 ; omega.
Qed.
 *)
Lemma ZofList_nth_mod_div : forall l (m:nat), Forall (fun x => 0 <= x < 2^n) l ->
  m < length l ->
  nth m l 0 = (ℤ.lst l) mod 2^(n*(S m)) / 2 ^ (n * m).
Proof.
  intros l m Hl Hlm.
  assert(length (take m l) = m).
    apply firstn_length_le ; omega.
  assert(Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ n) (take m l)).
    by apply Forall_take.
  assert((ℤ.lst take m l) < 2 ^ (n * m)).
    by apply ZofList_n_nn_bound_length.
  assert(0 <= ℤ.lst take m l).
  {
    apply ZofList_pos.
    unfold ZList_pos.
    eapply list.Forall_impl ; eauto.
    intros x Hx; simpl in Hx; omega.
  }
  assert(0 < 2 ^ (m*n)).
  {
    apply Z.pow_pos_nonneg. done.
    apply Z.mul_nonneg_nonneg; omega.
  }
  assert( 0 <= (ℤ.lst take m l) + nth m l 0 * 2 ^ (n * m)).
  {
    apply OMEGA2. done.
    apply Zmult_gt_0_le_0_compat.
    omega.
    apply Forall_nth_d.
    omega.
    eapply Forall_impl ; eauto ; intros x Hx ; simpl in Hx ; omega.
  }
  replace (ℤ.lst l) with ((ℤ.lst take m l) + 2^(n * Zlength (take m l)) * nth m l 0 + 2^(n * Zlength (take (S m) l)) * (ℤ.lst drop (S m) l)).
  2: by rewrite ZofList_take_nth_drop.
  replace (Zlength (take m l)) with (Z.of_nat m).
  2: rewrite Zlength_correct ; omega.
  replace (Zlength (take (S m) l)) with (Z.of_nat (S m)).
  2: rewrite Zlength_correct ; symmetry ; apply inj_eq ; apply firstn_length_le ; omega.
  rewrite -Zplus_mod_idemp_r.
  replace ((2 ^ (n * S m) * (ℤ.lst drop (S m) l)) `mod` 2 ^ (n * S m)) with 0.
  2: symmetry; rewrite Z.mul_comm ; apply Z_mod_mult.
  rewrite Z.add_0_r.
  rewrite Z.mod_small.
  Focus 2.
    split.
      rewrite Z.mul_comm; omega.
    - assert((ℤ.lst (take m l)) + 2 ^ (n * m) * nth m l 0 < 2 ^ (n * m) + 2 ^ (n * m) * nth m l 0).
        apply Zplus_lt_compat_r. omega.
      assert(2 ^ (n * m) + 2 ^ (n * m) * nth m l 0 <= 2 ^ (n * S m)).
        replace (n * S m) with (n * m + n).
        rewrite Zred_factor2 Z.pow_add_r ; try omega.
        apply Zmult_le_compat_l ; try omega.
        
        assert(minilemma : forall a b, a < b -> 1 + a <= b).
          intros ; omega.
        apply minilemma.
        eapply Forall_nth_d.
        apply Z.gt_lt.
        apply pown0.
        omega.
        eapply Forall_impl ; eauto ; intros x Hx ; simpl in Hx ; omega.
        apply Z.mul_nonneg_nonneg; omega.
        replace (Z.of_nat (S m)) with (Z.of_nat (m + 1)).
        rewrite Nat2Z.inj_add.
        ring.
        rewrite -plus_n_Sm.
        rewrite Nat.add_0_r.
        reflexivity.
      omega.
  rewrite Z.mul_comm.
  rewrite Z.Private_NZDiv.div_add ; try omega.
  rewrite Zdiv_small.
  omega.
  omega.
Qed.

Lemma ZofList_nth_last_div : forall l (m:nat), 
  S m = length l ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ n) (take m l) ->
  nth m l 0 = (ℤ.lst l) / 2 ^ (n * m).
Proof.
  intros.
  assert(length (take m l) = m).
    apply firstn_length_le ; omega.
  assert((ℤ.lst take m l) < 2 ^ (n * m)).
    by apply ZofList_n_nn_bound_length.
  assert(0 <= ℤ.lst take m l).
  {
    apply ZofList_pos.
    unfold ZList_pos.
    eapply list.Forall_impl ; eauto.
    intros x Hx; simpl in Hx; omega.
  }
  assert(0 < 2 ^ (m*n)).
  {
    apply Z.pow_pos_nonneg. done.
    apply Z.mul_nonneg_nonneg; omega.
  }
  replace (ℤ.lst l) with ((ℤ.lst take m l) + 2^(n * Zlength (take m l)) * nth m l 0 + 2^(n * Zlength (take (S m) l)) * (ℤ.lst drop (S m) l)).
  2: by rewrite ZofList_take_nth_drop.
  replace (Zlength (take m l)) with (Z.of_nat m).
  2: rewrite Zlength_correct ; omega.
  replace (Zlength (take (S m) l)) with (Z.of_nat (S m)).
  2: rewrite Zlength_correct ; symmetry ; apply inj_eq ; apply firstn_length_le ; omega.
  replace (2 ^ (n * S m) * (ℤ.lst drop (S m) l)) with 0.
  2: rewrite drop_ge ; simpl ; try omega; ring.
  rewrite -Zplus_0_r_reverse Z.mul_comm Z_div_plus ; try omega.
  rewrite Zdiv_small ; omega.
Qed.

End Integer.

