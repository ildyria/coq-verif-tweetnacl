Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.Export.

Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma addition: forall a b : Z,
  a < 2^n -> b < 2^n ->
    a + b < 2^Z.succ n.
Proof.
  intros.
  assert(H': 2 ^ Z.succ n = 2 * 2 ^ n) by (apply Z.pow_succ_r ; omega).
  orewrite H'.
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

Lemma ZofList_eq : forall l i, 0 <= i -> ZofListi l i = 2^(n * i) * ZofList l.
Proof. elim ; go => h l IHl i Hi /=.
  assert (H := Hi).
  apply IHl in H.
  rewrite -Zred_factor4 Z.mul_comm.
  f_equal.
  rewrite -Zmult_assoc_reverse -Zpower_exp ; go ; try omega.
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
    rewrite H Z.mul_comm ; go.
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

Lemma ZofList_app' : forall a b, ℤ.lst a ++ b = (ℤ.lst a) + 2^(n * ℤ.ℕ (length a)) * ℤ.lst b.
Proof. elim => [| h a Hl] b.
  - simpl ZofList.
    simpl length.
    rewrite -Zmult_0_r_reverse Z.pow_0_r ; omega.
  - simpl ZofList. 
    rewrite Hl Zplus_assoc_reverse.
    f_equal.
    rewrite <- Zred_factor4.
    f_equal.
    rewrite <- Zmult_assoc_reverse.
    assert(ℤ.ℕ length (h :: a) = ℤ.ℕ 1 + length a) by go ; rewrite H ; clear H.
    rewrite Nat2Z.inj_add.
    simpl.
    rewrite - Zred_factor4 Z.pow_add_r ; try omega.
    by rewrite Z.mul_1_r.
    nia.
Qed.

Lemma ZofList_app : forall a b, ℤ.lst a ++ b = (ℤ.lst a) + 2^(n * Zlength a) * ℤ.lst b.
Proof. elim => [| h a Hl] b /=.
  - rewrite Zlength_nil -Zmult_0_r_reverse Z.pow_0_r. omega.
  - rewrite Hl Zplus_assoc_reverse.
    f_equal.
    rewrite <- Zred_factor4.
    f_equal.
    rewrite <- Zmult_assoc_reverse.
    replace (Zlength (h :: a)) with(1 + Zlength a) by (rewrite Zlength_cons ; omega).
    rewrite -Zred_factor4 Z.pow_add_r ; try omega.
    rewrite Z.mul_1_r.
    go.
    assert(H:= Zlength_pos a).
    nia.
Qed.


Lemma ZofList_app_null: forall l, ℤ.lst l = ℤ.lst l ++ [0].
Proof. intro l ; rewrite ZofList_app ; simpl ; ring. Qed.

Theorem ZofList_transitive: forall (f g:list Z -> list Z) f' g' l l',
  ℤ.lst g l = g' (ℤ.lst l) ->
  ℤ.lst f l' = f' (ℤ.lst l') -> 
  g l = l' ->
  ℤ.lst f (g l) = f' (g' (ℤ.lst l)).
Proof. go. Qed.

Lemma ZofList_drop' : forall l (m:nat),
  2^(n * ℤ.ℕ length (take m l)) * (ℤ.lst drop m l) = (ℤ.lst l) - ℤ.lst take m l.
Proof. elim => [| z l IHl] m.
  - destr_boum m.
  - oreplace (2^(n * ℤ.ℕ length (take m (z::l))) * (ℤ.lst drop m (z :: l))) (2^(n * ℤ.ℕ length (take m (z::l))) * (ℤ.lst drop m (z :: l)) - (ℤ.lst take m (z :: l)) + (ℤ.lst take m (z :: l))).
    rewrite <- Z.add_sub_swap.
    f_equal.
    rewrite Z.add_comm -ZofList_app'.
    by replace(take m (z :: l) ++ drop m (z :: l)) with (z :: l) by (rewrite firstn_skipn ; reflexivity).
Qed.

Lemma ZofList_drop : forall l (m:nat),
  2^(n * Zlength (take m l)) * (ℤ.lst drop m l) = (ℤ.lst l) - ℤ.lst take m l.
Proof. elim => [|z l IHl] m.
  - destr_boum m.
  - oreplace (2^(n * Zlength (take m (z::l))) * (ℤ.lst drop m (z :: l))) (2^(n * Zlength (take m (z::l))) * (ℤ.lst drop m (z :: l)) - (ℤ.lst take m (z :: l)) + (ℤ.lst take m (z :: l))).
    rewrite <- Z.add_sub_swap.
    f_equal.
    rewrite Z.add_comm -ZofList_app.
    by replace(take m (z :: l) ++ drop m (z :: l)) with (z :: l) by (rewrite firstn_skipn ; reflexivity).
Qed.

Lemma ZofList_take' : forall l (m:nat),
  ℤ.lst take m l = (ℤ.lst l) - 2^(n * ℤ.ℕ length (take m l)) * ℤ.lst drop m l.
Proof. intros l m ; rewrite ZofList_drop' ; omega. Qed.

Lemma ZofList_take : forall l (m:nat),
  ℤ.lst take m l = (ℤ.lst l) - 2^(n * Zlength (take m l)) * ℤ.lst drop m l.
Proof. intros l m ; rewrite ZofList_drop ; omega. Qed.

Lemma ZofList_take_drop' : forall l (m:nat),
  (ℤ.lst take m l) + 2^(n * ℤ.ℕ length (take m l)) * (ℤ.lst drop m l) = ℤ.lst l.
Proof. intros l m ; rewrite ZofList_drop' ; go. Qed.

Lemma ZofList_take_drop : forall l (m:nat),
  (ℤ.lst take m l) + 2^(n * Zlength (take m l)) * (ℤ.lst drop m l) = ℤ.lst l.
Proof. intros l m ; rewrite ZofList_drop ; go. Qed.

Lemma ZofList_take_nth' : forall l (m:nat), (ℤ.lst take m l) + 2^(n * ℤ.ℕ length (take m l)) * nth m l 0 = ℤ.lst take (S m) l.
Proof. elim => [| z l IHl] [] ; flatten ; go.
  - destruct l ; flatten ; simpl ; go ;
    rewrite <-! Zmult_0_r_reverse ; ring.
  - move => m /=. 
    rewrite -IHl Zplus_assoc_reverse -Zred_factor4.
    f_equal ; f_equal ; rewrite -Zmult_assoc_reverse.
    f_equal ; rewrite -Z.pow_add_r ; go.
    f_equal ; nia.
Qed.

Lemma ZofList_take_nth : forall l (m:nat), (ℤ.lst take m l) + 2^(n * Zlength (take m l)) * nth m l 0 = ℤ.lst take (S m) l.
Proof.
  elim => [| z l IHl] [] ; flatten ; go.
  - destruct l ; flatten ; simpl ; go ;
    rewrite <-! Zmult_0_r_reverse ; ring.
  - move => m /=. rewrite Zlength_cons' -IHl Zplus_assoc_reverse -!Zred_factor4.
    f_equal ; f_equal ; rewrite -!Zmult_assoc_reverse.
    assert(H := Zlength_pos (take m l)).
    f_equal ; rewrite <- Z.pow_add_r ; try nia.
    f_equal ; nia.
Qed.


Lemma ZofList_take_nth_drop' : forall l (m:nat), (ℤ.lst take m l) + 2^(n * ℤ.ℕ length (take m l)) * nth m l 0 + 2^(n * ℤ.ℕ length (take (S m) l)) * (ℤ.lst drop (S m) l) = ℤ.lst l.
Proof.
  intros l m.
  rewrite ZofList_take_nth'.
  by rewrite ZofList_take_drop'.
Qed.

Lemma ZofList_take_nth_drop : forall l (m:nat), (ℤ.lst take m l) + 2^(n * Zlength (take m l)) * nth m l 0 + 2^(n * Zlength (take (S m) l)) * (ℤ.lst drop (S m) l) = ℤ.lst l.
Proof.
  intros l m.
  rewrite ZofList_take_nth.
  by rewrite ZofList_take_drop.
Qed.

Lemma ZofList_upd_nth_length : forall l (m:nat) v,
      (m < length l)%nat ->
      ℤ.lst (upd_nth m l v) = (ℤ.lst l) + 2^(n*m) * (-nth m l 0 + v).
Proof.
  elim => [| z l IHl]  [|m] v Hml.
  1,3: change_Z_of_nat ; rewrite -?Zmult_0_r_reverse.
  1: simpl ; rewrite -?Zmult_0_r_reverse.
  all: rewrite ?Z.pow_0_r.
  omega.
  simpl; omega.
  simpl in Hml; omega.
  simpl in Hml.
  assert((m < length l)%nat).
  omega.
  simpl upd_nth; simpl ZofList.
  rewrite IHl //.
  rewrite -Zred_factor4.
  rewrite Z.add_assoc.
  f_equal.
  rewrite Z.mul_assoc.
  f_equal.
  rewrite -Z.pow_add_r ; try omega.
  f_equal.
  replace (Z.of_nat (S m)%nat) with (1 + Z.of_nat m).
  ring.
  simpl ; rewrite Zpos_P_of_succ_nat ; omega.
  rewrite Z.mul_comm.
  apply Zmult_gt_0_le_0_compat ; try omega.
Qed.

Lemma ZofList_upd_nth_Zlength : forall l (m:nat) v,
      m < Zlength l ->
      ℤ.lst (upd_nth m l v) = (ℤ.lst l) + 2^(n*m) * (-nth m l 0 + v).
Proof. convert_length_to_Zlength ZofList_upd_nth_length. Qed.

End Integer.

Lemma destruct_length_16 : forall (l:list Z), (length l = 16)%nat -> exists z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14,
l = [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14].
Proof. move => l Hl. repeat (destruct l ; tryfalse).
repeat eexists.
Qed.

Lemma destruct_Zlength_16 : forall (l:list Z), Zlength l = 16 -> exists z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14,
l = [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14].
Proof.
intros l Hl.
rewrite Zlength_correct in Hl.
apply destruct_length_16.
omega.
Qed.











Close Scope Z.

Notation "ℤ16.lst A" := (ZofList 16 A) (at level 65, right associativity).

