Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.Unpack25519.
Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Fixpoint unpack_for (l:list Z) : list Z := match l with
  | [] => []
  | h :: [] => [h]
  | a :: b :: q => (a + 2^n * b) :: unpack_for q
  end.

Lemma unpack_for_nth : forall (i:nat) (l:list Z), nth i (unpack_for l) 0 = nth (2 * i) l 0 + 2 ^ n * nth (2 * i + 1) l 0.
Proof.
  elim=> [|i iH] [|l q] /= ; try omega.
  flatten => /= ; ring.
  flatten => /= ; replace (i + S(i + 0))%nat with (S (2*i))%nat by omega.
  flatten ; ring.
  destruct i; destruct l ; rewrite iH ; simpl ; flatten ; simpl; ring.
Qed.

End Integer.

Lemma Unpack_for_ind_step: forall n, 0 < n ->
  forall l, ZofList (2*n) (unpack_for n l) = ZofList n l ->
  forall a b, ZofList (2*n) (unpack_for n ( a :: b :: l)) = ZofList n (a :: b :: l).
Proof.
  intros n Hn l Hl a b.
  simpl.
  rewrite Hl.
  rewrite <- Z.add_assoc.
  f_equal.
  rewrite  <-Zred_factor4.
  f_equal.
  replace ( 2* n ) with (n + n) by omega.
  orewrite Zpower_exp; ring.
Qed.

Lemma Unpack_for_correct: forall n, 0 < n -> forall l, ZofList (2*n) (unpack_for n l) = ZofList n l.
Proof.
intros n Hn l.
induction l using list_ind_by_2.
reflexivity.
simpl. omega.
apply Unpack_for_ind_step ; assumption.
Qed.

Lemma Unpack_for_length : forall n, 0 < n -> forall l m , length l = m -> even m = true -> length (unpack_for n l) = Nat.div m 2.
Proof.
  intros n Hn. induction l using list_ind_by_2 ; intros.
  simpl in H.
  subst m.
  reflexivity.
  simpl in H.
  subst m.
  inversion H0.
  simpl unpack_for.
  simpl length in *.
  subst m.
  simpl in H0.
  replace (S (S (length l))) with (length l + 1*2)%nat by omega.
  orewrite NPeano.Nat.div_add.
  replace (length l `div` 2 + 1)%nat with (S (length l `div` 2))%nat by omega.
  f_equal.
  apply IHl ; auto.
Qed.

Definition mask0x7FFF' (x:Z) : Z := Z.land x (Z.pow 2 15 - 1).
Definition mask0x7FFF (x:Z) : Z := Z.land x 32767.

Lemma mask0x7FFF_eq: forall x, mask0x7FFF x = mask0x7FFF' x.
Proof. reflexivity. Qed.

Lemma mask0x7FFF_fixpoint: forall x, 0 <= x < Z.pow 2 15 -> mask0x7FFF' x = x.
Proof.
intros x Hx.
unfold mask0x7FFF'.
change (2^15 - 1) with (Z.ones 15).
apply Z.land_ones_low.
omega.
destruct Hx as [H0 H15].
apply Z.le_lteq in H0.
destruct H0 as [H0|H0].
apply Z.log2_lt_pow2.
omega.
omega.
assert(Z.log2 x <= x).
apply Z.log2_le_lin.
omega.
subst x.
omega.
Qed.

Lemma mask0x7FFF_bounded: forall x, 0 <= x-> 0 <= mask0x7FFF x < 2^16.
Proof.
move=> x Hx.
split.
apply Z.land_nonneg.
go.
apply Z.log2_lt_cancel.
unfold mask0x7FFF.
assert(H32767: 0 ≤ 32767) by (compute; go).
assert(H:= Z.log2_land x 32767 Hx H32767).
assert(Z.min (Z.log2 x) (Z.log2 32767) <= 14).
replace (Z.log2 32767) with 14.
apply Z.le_min_r.
reflexivity.
change(Z.log2 (2^16)) with 16.
omega.
Qed.

Lemma Sumbounded215: forall a b, 0 <= a < 2^7 -> 0 <= b < 2^8 -> 0 <= a * 2^8 + b < 2^15.
Proof.
intros.
split.
replace b with (b*1) by omega.
apply OMEGA7; try omega.
assert(a <= 2^7 - 1) by omega.
assert(b <= 2^8 - 1) by omega.
assert(a * 2^8 <= (2^7 - 1) * 2^8).
apply Zmult_le_compat_r ; omega.
assert(a * 2^8 + b <= (2^7 - 1) * 2^8 + 2^8 - 1) by omega.
assert((2 ^ 7 - 1) * 2 ^ 8 + 2 ^ 8 - 1 < 2^15) by reflexivity.
omega.
Qed.

Lemma Sumbounded216: forall a b, 0 <= a < 2^8 -> 0 <= b < 2^8 -> 0 <= a * 2^8 + b < 2^16.
Proof.
intros.
split.
replace b with (b*1) by omega.
apply OMEGA7; try omega.
assert(a <= 2^8 - 1) by omega.
assert(a * 2^8 <= (2^8 - 1) * 2^8) by (apply Zmult_le_compat_r ; omega).
assert(a * 2^8 + b <= (2^8 - 1) * 2^8 + 2^8 - 1) by omega.
assert((2 ^ 8 - 1) * 2 ^ 8 + 2 ^ 8 - 1 < 2^16) by reflexivity.
omega.
Qed.

Close Scope Z.

Corollary Unpack_for_length_16_32 : forall l, length l = 32 -> length (unpack_for 8 l) = 16.
Proof.
intros.
rewrite (Unpack_for_length 8 _ _ 32) ; go.
Qed.

Open Scope Z.

Corollary Unpack_for_Zlength_16_32 : forall l, Zlength l = 32 -> Zlength (unpack_for 8 l) = 16.
Proof. convert_length_to_Zlength Unpack_for_length_16_32. Qed.

Lemma unpack_for_bounded : forall l, Forall (fun x : ℤ => 0 <= x < 2 ^ 8) l ->  Forall (fun x : ℤ => 0 <= x < 2 ^ 16) (unpack_for 8 l).
Proof.
assert(2^8 < 2^16) by reflexivity.
induction l using list_ind_by_2 ; intros ; simpl.
by rewrite Forall_nil.
apply Forall_cons in H0 ; destruct H0 as [Ha _].
apply Forall_cons_2. omega.
by rewrite Forall_nil.
apply Forall_cons in H0 ; destruct H0 as [Ha H0].
apply Forall_cons in H0 ; destruct H0 as [Hb Hl].
apply IHl in Hl.
apply Forall_cons_2 ; auto.
rewrite Z.add_comm.
rewrite Z.mul_comm.
by apply Sumbounded216.
Qed.

Lemma upd_nth_mask0x7FFF_bounded : forall l, Forall (fun x : Z => 0 <= x < 2 ^16) l -> Forall (fun x : Z => 0 <= x < 2 ^16) (upd_nth 15 l (mask0x7FFF (nth 15 l 0))).
Proof.
intros.
apply upd_nth_Forall => //=.
apply mask0x7FFF_bounded.
apply Forall_nth_d.
omega.
eapply Forall_impl.
apply H.
intros ; go.
Qed.

Definition Unpack25519 l := upd_nth 15 (unpack_for 8 l) (mask0x7FFF (nth 15 (unpack_for 8 l) 0)).

Lemma Unpack25519' : forall l,
  (length l = 32)%nat ->
  Forall (fun x : ℤ => 0 <= x < 2 ^ 8) l ->
  ZofList 8 (upd_nth 31 l (Z.land (nth 31 l 0) 127)) = ZUnpack25519 (ZofList 8 l).
Proof.
  move => l Hl Up8Bounded.
  rewrite /ZUnpack25519.
  replace (Z.ones 255) with (ZofList 8 [255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;255;127]).
  2: compute ; reflexivity.
  rewrite Zlist_and_ZofList.
  2: reflexivity.
  2: assumption.
  2: repeat apply list.Forall_cons_2 ; try apply list.Forall_nil ; compute ; go.
  f_equal.
  do 33 (destruct l ; tryfalse).
  simpl nth.
  simpl upd_nth.
  rewrite /Zlist_and.
  simpl Zipp.
  assert(HX: forall x, 0 <= x < 2^8 -> Z.land x (Z.ones 8) = x).
  {
  intros ; rewrite Z.land_ones ; try apply Z.mod_small ; omega.
  }
  change (255) with (Z.ones 8).
  repeat (apply list.Forall_cons_1 in Up8Bounded ; destruct Up8Bounded as [? Up8Bounded]).
  repeat (rewrite HX ; [|assumption]).
  reflexivity.
Qed.

Lemma Unpack25519'_Zlength : forall l,
  Zlength l = 32 ->
  Forall (fun x : ℤ => 0 <= x < 2 ^ 8) l ->
  ZofList 8 (upd_nth 31 l (Z.land (nth 31 l 0) 127)) = ZUnpack25519 (ZofList 8 l).
Proof. convert_length_to_Zlength Unpack25519'. Qed.

Lemma Unpack25519_bounded : forall l, Forall (fun x : ℤ => 0 <= x < 2 ^ 8) l ->  Forall (fun x : ℤ => 0 <= x < 2 ^ 16) (Unpack25519 l).
Proof.
move=> l H ; rewrite /Unpack25519.
by apply upd_nth_mask0x7FFF_bounded, unpack_for_bounded.
Qed.

Close Scope Z.

Lemma Unpack25519_length : forall l, length l = 32 -> length (Unpack25519 l) = 16.
Proof. intros ; rewrite /Unpack25519 upd_nth_length Unpack_for_length_16_32 ; omega. Qed.

Open Scope Z.

Lemma Unpack25519_Zlength : forall l, Zlength l = 32 -> Zlength (Unpack25519 l) = 16.
Proof. convert_length_to_Zlength Unpack25519_length. Qed.

Lemma Unpack25519_eq_ZUnpack25519 : forall l,
  (length l = 32)%nat ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) l ->
  ZUnpack25519 (ZofList 8 l) = ZofList 16 (Unpack25519 l).
Proof.
  intros l Hlength Hbound.
  rewrite /Unpack25519.
  rewrite -Unpack_for_correct //.
  change (2 * 8) with 16.
  assert(Up8Bounded := unpack_for_bounded l Hbound).
  assert(Up8Length := Unpack_for_length_16_32 l Hlength).
  remember (unpack_for 8 l) as l'.
  clear l Hlength Hbound Heql'.
  rewrite /ZUnpack25519.
  replace (Z.ones 255) with (ℤ16.lst [65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;32767]).
  2: compute ; reflexivity.
  rewrite Zlist_and_ZofList.
  2: reflexivity.
  2: assumption.
  2: repeat apply list.Forall_cons_2 ; try apply list.Forall_nil ; compute ; go.
  f_equal.
  unfold mask0x7FFF.
  do 17 (destruct l' ; tryfalse).
  simpl nth.
  simpl upd_nth.
  rewrite /Zlist_and.
  simpl Zipp.
  assert(HX: forall x, 0 <= x < 2^16 -> Z.land x (Z.ones 16) = x).
  {
  intros ; rewrite Z.land_ones ; try apply Z.mod_small ; omega.
  }
  change (65535) with (Z.ones 16).
  repeat (apply list.Forall_cons_1 in Up8Bounded ; destruct Up8Bounded as [? Up8Bounded]).
  repeat (rewrite HX ; [|assumption]).
  reflexivity.
Qed.

Lemma Unpack25519_eq_ZUnpack25519_Zlength : forall l,
  Zlength l = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) l ->
  ZUnpack25519 (ZofList 8 l) = ZofList 16 (Unpack25519 l).
Proof. convert_length_to_Zlength Unpack25519_eq_ZUnpack25519. Qed.

Close Scope Z.
