Require Import stdpp.prelude.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.

Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Fixpoint pack_for (l:list Z) : list Z := match l with
  | [] => []
  | a :: q => a mod 2^n :: a / 2 ^ n :: pack_for q
  end.

Lemma pack_for_nth_e : forall (i:nat) (l:list Z), nth (2*i) (pack_for l) 0 = nth i l 0 mod 2 ^ n.
Proof.
  elim=> [|i iH] [|l q] //; try omega.
  simpl.
  flatten ; try omega.
  assert((n0 = 2* i) %nat) by omega.
  go.
Qed.

Lemma pack_for_nth_o : forall (i:nat) (l:list Z), nth (2*i + 1) (pack_for l) 0 = nth i l 0 / 2 ^ n.
Proof.
  elim=> [|i iH] [|l q] //; try omega.
  simpl.
  flatten ; try omega.
  assert((n0 = 2* i + 1) %nat) by omega.
  go.
Qed.

End Integer.

Lemma pack_for_ind_step: forall n, 0 < n ->
  forall l, ZofList n (pack_for n l) = ZofList (2*n) l ->
  forall a, ZofList n (pack_for n ( a :: l)) = ZofList (2*n) (a :: l).
Proof.
  intros n Hn l Hl a.
  simpl.
  rewrite Hl.
  rewrite  <-Zred_factor4.
  rewrite Z.add_assoc.
  replace (a `mod` 2 ^ n + 2 ^ n * a `div` 2 ^ n) with a.
  f_equal.
  replace ( 2* n ) with (n + n) by omega.
  orewrite Zpower_exp; ring.
  rewrite Z.add_comm.
  apply Z_div_mod_eq.
  apply pown0 ; omega.
Qed.

Lemma pack_for_correct: forall n, 0 < n -> forall l, ZofList n (pack_for n l) = ZofList (2*n)  l.
Proof.
intros n Hn l.
induction l.
reflexivity.
simpl.
apply pack_for_ind_step ; assumption.
Qed.

Lemma pack_for_length : forall n, 0 < n -> forall l m , length l = m -> length (pack_for n l) = Nat.mul m 2.
Proof.
  intros n Hn.
  induction l; intros ; go.
  rewrite -H.
  go.
Qed.

Close Scope Z.

Corollary pack_for_length_32_16 : forall l, length l = 16 -> length (pack_for 8 l) = 32.
Proof.
intros.
rewrite (pack_for_length 8 _ _ 16) ; go.
Qed.

Open Scope Z.

Corollary pack_for_Zlength_32_16 : forall l, Zlength l = 16 -> Zlength (pack_for 8 l) = 32.
Proof. convert_length_to_Zlength pack_for_length_32_16. Qed.

Lemma unpack_for_bounded : forall l, Forall (fun x : ℤ => 0 <= x < 2 ^ 16) l ->  Forall (fun x : ℤ => 0 <= x < 2 ^ 8) (pack_for 8 l).
Proof.
induction l ; intros ; simpl.
by rewrite Forall_nil.
apply Forall_cons in H ; destruct H as [Ha Haa].
repeat apply Forall_cons_2 ; [ | | auto].
apply Z_mod_lt ; go.
split.
apply Z_div_pos ; go.
apply Zdiv_lt_upper_bound ; change (2 ^ 8 * 2 ^ 8) with (2 ^ 16) ; go.
Qed.

Close Scope Z.
