Require Export Tools.
Require Export notations.

Open Scope Z.

Import ListNotations.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma addition: forall a b : Z,
  a < 2^n ->
  b < 2^n ->
  a + b < 2^Z.succ n.
Proof.
  intros a b Ha Hb.
  assert(H: 2 ^ Z.succ n = 2 * 2 ^ n) by (apply Z.pow_succ_r ; omega).
  rewrite H.
  omega.
Qed.

(* By J-M Madiot *)
Lemma addition': forall a b : Z, a < 2^63 -> b < 2^63 -> a + b < 2^64.
Proof.
  change (2 ^ 64) with (2 ^ 63 * 2).
  intros; omega.
Qed.


Fixpoint ZofListi (a: list Z) (i:Z) : Z := match a with 
| [] => 0
| h :: q => h * Z.pow 2 (n * i) + ZofListi q (Z.succ i)
end.

Fixpoint ZofList (a : list Z) : Z := match a with 
| [] => 0
| h :: q => h + Z.pow 2 n * ZofList q
end.
Notation "ℤ.lst A" := (ZofList A) (at level 65, right associativity).

Lemma pown: 2 ^ n > 1.
Proof. rewrite Z.gt_lt_iff ; apply Z.pow_gt_1 ; try omega. Qed.

Lemma pown0: 2 ^ n > 0.
Proof. assert(Hp:= pown) ; omega. Qed.

Lemma ZofList_eq : forall l i, i >= 0 -> ZofListi l i = 2^(n * i) * ZofList l.
Proof.
  dependent induction l; go.
  intros i Hi.
  unfold ZofListi ; fold ZofListi.
  unfold ZofList ; fold ZofList.
  assert (H := Hi).
  apply IHl in H.
  rewrite <- Zred_factor4.
  rewrite Z.mul_comm.
  f_equal.
  rewrite <- Zmult_assoc_reverse.
  rewrite <- Zpower_exp ; go ; try omega.
  rewrite Zmult_succ_r_reverse.
  go.
  apply Z.ge_le_iff.
  rewrite Zmult_comm.
  apply Zmult_gt_0_le_0_compat ; omega.
Qed.


Corollary ZofList_equiv : forall l, ZofListi l 0 = ZofList l.
Proof.
  intro l.
  assert (2^(n * 0) = 1) by (rewrite <- Zmult_0_r_reverse ; go).
  assert (ZofList l = 2^(n * 0) * ZofList l).
    rewrite H.
    rewrite Z.mul_comm ; go.
  rewrite H0.
  apply ZofList_eq.
  omega.
Qed.

Lemma ZofList_nil : ℤ.lst nil = 0.
Proof. go. Qed.

Lemma ZofList_cons_0 : forall a, ℤ.lst [a] = a.
Proof. intros a ; go. Qed.

Lemma ZofList_cons : forall a b, ℤ.lst a :: b = a + 2^n * ℤ.lst b.
Proof. intros a b ; go. Qed.

Lemma ZofList_add : forall m a b, ℤ.lst m + a :: b = m + ℤ.lst a :: b.
Proof. intros m a b ; go. Qed.

Lemma ZofList_app : forall a b, ℤ.lst a ++ b = (ℤ.lst a) + 2^(n * ℤ.ℕ (length a)) * ℤ.lst b.
Proof.
  induction a as [| h a Hl].
  - intro b.
    rewrite ZofList_nil.
    assert ([] ++ b = b) by apply app_nill_l. rewrite H ; go ; clear H.
    assert (ℤ.ℕ length (nil:(list Z)) = 0) by go. rewrite H ; go ; clear H.
    rewrite <- Zmult_0_r_reverse.
    rewrite Z.pow_0_r.
    omega.
  - intro b.
    assert ((h::a) ++ b = h :: a ++ b) by apply consApp2 ; rewrite H ; clear H.
    unfold ZofList; fold ZofList.
    rewrite Hl.
    rewrite Zplus_assoc_reverse.
    f_equal.
    rewrite <- Zred_factor4.
    f_equal.
    rewrite <- Zmult_assoc_reverse.
    assert(ℤ.ℕ length (h :: a) = ℤ.ℕ 1 + length a) by go ; rewrite H ; clear H.
    rewrite Nat2Z.inj_add.
    assert(ℤ.ℕ 1 = 1) by go ; rewrite H ; clear H.
    rewrite <- Zred_factor4.
    rewrite Z.pow_add_r ; try omega.
    assert(n * 1 = n) by go ; rewrite H ; clear H.
    go.
    rewrite Z.mul_comm.
    apply Zmult_gt_0_le_0_compat ; omega.
Qed.

Lemma ZofList_app_null: forall l, ℤ.lst l = ℤ.lst l ++ [0].
Proof. intro l ; rewrite ZofList_app ; simpl ; ring. Qed.

Theorem ZofList_transitive: forall (f g:list Z -> list Z) f' g' l l',
  ℤ.lst g l = g' (ℤ.lst l) ->
  ℤ.lst f l' = f' (ℤ.lst l') -> 
  g l = l' ->
  ℤ.lst f (g l) = f' (g' (ℤ.lst l)).
Proof. go. Qed.

Lemma ZofList_tail : forall l (m:nat),
  2^(n * ℤ.ℕ length (slice m l)) * (ℤ.lst tail m l) = (ℤ.lst l) - ℤ.lst slice m l.
Proof.
  intros l; destruct l; intros m.
  - simpl.
    rewrite slice_length_le ; go.
    rewrite tail_length_le ; go.
  - assert(HS: 2^(n * ℤ.ℕ length (slice m (z::l))) * (ℤ.lst tail m (z :: l)) = 2^(n * ℤ.ℕ length (slice m (z::l))) * (ℤ.lst tail m (z :: l)) - (ℤ.lst slice m (z :: l)) + (ℤ.lst slice m (z :: l))) by omega ;  rewrite HS ; clear HS.
    rewrite <- Z.add_sub_swap.
    f_equal.
    rewrite Z.add_comm.
    rewrite <- ZofList_app ; go.
    assert(HS: slice m (z :: l) ++ tail m (z :: l) = z :: l) by apply slice_tail_app ; rewrite HS ; clear HS.
    go.
Qed.

Lemma ZofList_slice : forall l (m:nat),
  ℤ.lst slice m l = (ℤ.lst l) - 2^(n * ℤ.ℕ length (slice m l)) * ℤ.lst tail m l.
Proof. intros l m ; rewrite ZofList_tail ; omega. Qed.

Lemma ZofList_slice_tail : forall l (m:nat),
  (ℤ.lst slice m l) + 2^(n * ℤ.ℕ length (slice m l)) * (ℤ.lst tail m l) = ℤ.lst l.
Proof. intros l m ; rewrite ZofList_tail ; go. Qed.

Lemma ZofList_slice_nth : forall l (m:nat), (ℤ.lst slice m l) + 2^(n * ℤ.ℕ length (slice m l)) * nth m l 0 = ℤ.lst slice (S m) l.
Proof.
  induction l ; destruct m ; flatten ; simpl ; go.
  - destruct l ; flatten ; simpl ; go ;
    rewrite <-! Zmult_0_r_reverse ; ring.
  - flatten.
    + simpl ; flatten ; simpl ; rewrite <-! Zmult_0_r_reverse ; try rewrite <- Zred_factor0  ; ring.
    + rewrite Zplus_assoc_reverse.
      f_equal.
      rewrite Zpos_P_of_succ_nat.
      replace (n * Z.succ (ℤ.ℕ length (slice m (z :: l0)))) with (n + n * ℤ.ℕ length (slice m (z :: l0))) by ring.
      rewrite Z.pow_add_r ; go.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      f_equal ; go.
Qed.

Lemma ZofList_slice_nth_tail : forall l (m:nat), (ℤ.lst slice m l) + 2^(n * ℤ.ℕ length (slice m l)) * nth m l 0 + 2^(n * ℤ.ℕ length (slice (S m) l)) * (ℤ.lst tail (S m) l) = ℤ.lst l.
Proof.
  Proof.
  intros l m.
  rewrite ZofList_slice_nth.
  rewrite ZofList_slice_tail.
  go.
Qed.

End Integer.

Close Scope Z.

Notation "ℤ16.lst A" := (ZofList 16 A) (at level 65, right associativity).

