Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.M.
Require Export Tweetnacl_verif.verif_M_compute_pre.

Local Open Scope Z.


Local Instance term_dec : Decidable := 
{
  decide := term_decide;
  denote := term_denote;
  decide_impl := term_decide_impl
}.

Local Instance expr_dec : Decidable := 
{
  decide := expr_decide;
  denote := expr_denote;
  decide_impl := expr_decide_impl
}.

Local Instance list_expr_dec : Decidable := Build_Decidable
  (list expr) (list Z) 
  (list_decide) (list_denote) (list_decide_impl).

Local Instance list_term_dec : Decidable := Build_Decidable
  (list term) (list Z) 
  (list_decide) (list_denote) (list_decide_impl).

Local Ltac solve_this_thing_please_autorewrite i j:= 
    subst i;
    let H' := fresh in
    gen_i H' j ; simpl;
    repeat orewrite inner_M_i_j_eq;
    repeat orewrite Znth_nth;
    unfold nat_of_Z;
    simpl;
    unfold update_M_i_j';
    unfold local_update_M; simpl; 
    autorewrite with innerouterMdb;
    repeat orewrite upd_Znth_upd_nth;
    simpl;
    mini_ring.

Lemma outer_M_fix_i_1' : forall i j contents_a contents_b,
Zlength contents_a = 16 ->
Zlength contents_b = 16 ->
0 <= i < 4 ->
0 <= j < 16 ->
0 < i ->
outer_M_fix (i - 1) 16 contents_a contents_b
  (inner_M_fix i (j + 1)
     (option.from_option id 0 (base.lookup (Z.to_nat i) contents_a))
     contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0]) =
upd_Znth (i + j)
  (outer_M_fix i j contents_a contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0])
  (Znth (i + j)
     (outer_M_fix i j contents_a contents_b
        [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0; 0]) 0 +
   Znth i contents_a 0 * Znth j contents_b 0).
Proof.
  intros i j a b Ha Hb Hi Hj Hii.
  rewrite Zlength_correct in Ha.
  rewrite Zlength_correct in Hb.
  assert(Ha' : (length a = 16)%nat) by go.
  assert(Hb' : (length b = 16)%nat) by go.
  repeat (destruct a ; tryfalse).
  repeat (destruct b ; tryfalse).
  rewrite <- Zlength_correct in *.
  rewrite (outer_M_fix_equation i).
  flatten.
    apply Z.leb_le in Eq ; omega.
    clear Eq.
  assert_gen_hyp_ H i 3 3. omega.
    destruct H ; try (subst i ; omega).
  Opaque outer_M_fix.
    repeat (destruct H ; [solve_this_thing_please_autorewrite i j|]).
    solve_this_thing_please_autorewrite i j.
Qed.

Lemma outer_M_fix_i_1'' : forall i j contents_a contents_b,
Zlength contents_a = 16 ->
Zlength contents_b = 16 ->
4 <= i < 8 ->
0 <= j < 16 ->
0 < i ->
outer_M_fix (i - 1) 16 contents_a contents_b
  (inner_M_fix i (j + 1)
     (option.from_option id 0 (base.lookup (Z.to_nat i) contents_a))
     contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0]) =
upd_Znth (i + j)
  (outer_M_fix i j contents_a contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0])
  (Znth (i + j)
     (outer_M_fix i j contents_a contents_b
        [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0; 0]) 0 +
   Znth i contents_a 0 * Znth j contents_b 0).
Proof.
  intros i j a b Ha Hb Hi Hj Hii.
  rewrite Zlength_correct in Ha.
  rewrite Zlength_correct in Hb.
  assert(Ha' : (length a = 16)%nat) by go.
  assert(Hb' : (length b = 16)%nat) by go.
  repeat (destruct a ; tryfalse).
  repeat (destruct b ; tryfalse).
  rewrite <- Zlength_correct in *.
  rewrite (outer_M_fix_equation i).
  flatten.
    apply Z.leb_le in Eq ; omega.
    clear Eq.
  assert(H: i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by omega.
  Opaque outer_M_fix.
    repeat (destruct H ; [solve_this_thing_please_autorewrite i j|]).
    solve_this_thing_please_autorewrite i j.
Qed.

Lemma outer_M_fix_i_1''' : forall i j contents_a contents_b,
Zlength contents_a = 16 ->
Zlength contents_b = 16 ->
8 <= i < 12 ->
0 <= j < 16 ->
0 < i ->
outer_M_fix (i - 1) 16 contents_a contents_b
  (inner_M_fix i (j + 1)
     (option.from_option id 0 (base.lookup (Z.to_nat i) contents_a))
     contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0]) =
upd_Znth (i + j)
  (outer_M_fix i j contents_a contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0])
  (Znth (i + j)
     (outer_M_fix i j contents_a contents_b
        [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0; 0]) 0 +
   Znth i contents_a 0 * Znth j contents_b 0).
Proof.
  intros i j a b Ha Hb Hi Hj Hii.
  rewrite Zlength_correct in Ha.
  rewrite Zlength_correct in Hb.
  assert(Ha' : (length a = 16)%nat) by go.
  assert(Hb' : (length b = 16)%nat) by go.
  repeat (destruct a ; tryfalse).
  repeat (destruct b ; tryfalse).
  rewrite <- Zlength_correct in *.
  rewrite (outer_M_fix_equation i).
  flatten.
    apply Z.leb_le in Eq ; omega.
    clear Eq.
  assert(H: i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by omega.
  Opaque outer_M_fix.
    repeat (destruct H ; [solve_this_thing_please_autorewrite i j|]).
    solve_this_thing_please_autorewrite i j.
Qed.

Lemma outer_M_fix_i_1'''' : forall i j contents_a contents_b,
Zlength contents_a = 16 ->
Zlength contents_b = 16 ->
12 <= i < 16 ->
0 <= j < 16 ->
0 < i ->
outer_M_fix (i - 1) 16 contents_a contents_b
  (inner_M_fix i (j + 1)
     (option.from_option id 0 (base.lookup (Z.to_nat i) contents_a))
     contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0]) =
upd_Znth (i + j)
  (outer_M_fix i j contents_a contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0])
  (Znth (i + j)
     (outer_M_fix i j contents_a contents_b
        [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0; 0]) 0 +
   Znth i contents_a 0 * Znth j contents_b 0).
Proof.
  intros i j a b Ha Hb Hi Hj Hii.
  rewrite Zlength_correct in Ha.
  rewrite Zlength_correct in Hb.
  assert(Ha' : (length a = 16)%nat) by go.
  assert(Hb' : (length b = 16)%nat) by go.
  repeat (destruct a ; tryfalse).
  repeat (destruct b ; tryfalse).
  rewrite <- Zlength_correct in *.
  rewrite (outer_M_fix_equation i).
  flatten.
    apply Z.leb_le in Eq ; omega.
    clear Eq.
  assert(H: i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by omega.
(*   assert(H: i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12) by omega. *)
  Opaque outer_M_fix.
    repeat (destruct H ; [solve_this_thing_please_autorewrite i j|]).
    solve_this_thing_please_autorewrite i j.
Qed.

Lemma outer_M_fix_i_1 : forall i j contents_a contents_b,
Zlength contents_a = 16 ->
Zlength contents_b = 16 ->
0 <= i < 16 ->
0 <= j < 16 ->
0 < i ->
outer_M_fix (i - 1) 16 contents_a contents_b
  (inner_M_fix i (j + 1)
     (option.from_option id 0 (base.lookup (Z.to_nat i) contents_a))
     contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0]) =
upd_Znth (i + j)
  (outer_M_fix i j contents_a contents_b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0])
  (Znth (i + j)
     (outer_M_fix i j contents_a contents_b
        [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0; 0]) 0 +
   Znth i contents_a 0 * Znth j contents_b 0).
Proof.
  intros i j a b Ha Hb Hi Hj Hii.
  assert(H: i < 4 \/ 4 <= i < 8 \/  8 <= i < 12 \/ 12 <= i) by omega.
  destruct H.
  apply outer_M_fix_i_1' ; go.
  destruct H.
  apply outer_M_fix_i_1'' ; go.
  destruct H.
  apply outer_M_fix_i_1''' ; go.
  apply outer_M_fix_i_1'''' ; go.
Qed.


Close Scope Z.
