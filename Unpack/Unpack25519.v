Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import mathcomp.ssreflect.ssreflect.
Require Import stdpp.prelude.


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
  elim=> [|i iH] [|l q] /=.
  omega.
  flatten => /= ; ring.
  ring.
  flatten => /= ; replace (i + S(i + 0))%nat with (S (2*i))%nat by omega.
  ro mega.
  ; ring.
  flatten.
  ring.
  move => 
  induction i; intros.
destruct l ; simpl ; flatten ; simpl ; ring.
destruct l ; simpl ; flatten.
omega.
simpl ; flatten ; omega.
replace (i + S(i + 0))%nat with (S (2 * i))%nat by omega.
replace (S(2 * i) + 1)%nat with (S (2 * i + 1))%nat by omega.
simpl nth.
rewrite IHi.
reflexivity.
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
  rewrite Zpower_exp by omega. ring.
Qed.

Lemma Unpack25519_correct: forall n, 0 < n -> forall l, ZofList (2*n) (unpack_for n l) = ZofList n l.
Proof.
intros n Hn l.
induction l using list_ind_by_2.
reflexivity.
simpl. omega.
apply Unpack_for_ind_step ; assumption.
Qed.

Lemma Unpack25519_length : forall n, 0 < n -> forall l m , length l = m -> even m = true -> length (unpack_for n l) = Nat.div m 2.
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
  rewrite NPeano.Nat.div_add by omega.
  replace (length l `div` 2 + 1)%nat with (S (length l `div` 2))%nat by omega.
  f_equal.
  apply IHl ; auto.
Qed.

Definition mask0x7FFF (x:Z) : Z := Z.land x (Z.pow 2 15 - 1).
Definition mask0x7FFF' (x:Z) : Z := Z.land x 32767.

Lemma mask0x7FFF_eq: forall x, mask0x7FFF x = mask0x7FFF' x.
Proof. reflexivity. Qed.

Lemma mask0x7FFF_fixpoint: forall x, 0 <= x < Z.pow 2 15 -> mask0x7FFF x = x.
Proof.
intros x Hx.
unfold mask0x7FFF.
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

Close Scope Z.

Corollary Unpack25519_length_16_32 : forall l, length l = 32 -> length (unpack_for 8 l) = 16.
Proof.
intros.
rewrite (Unpack25519_length 8) with (m:=32).
reflexivity.
omega.
assumption.
reflexivity.
Qed.

Close Scope Z.
