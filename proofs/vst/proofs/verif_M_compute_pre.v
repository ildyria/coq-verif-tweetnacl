Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.Inner_M1.

Open Scope Z.

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
    gen_i H' j ; Grind_add_Z;
    repeat orewrite inner_M_i_j_eq;
    repeat orewrite Znth_nth;
    unfold nat_of_Z;
    change_Z_to_nat;
    simpl;
    unfold update_M_i_j';
    unfold local_update_M; simpl; 
    autorewrite with innerouterMdb;
    repeat orewrite upd_Znth_upd_nth;
    simpl;
    repeat rewrite Z.add_0_r;
    repeat rewrite Z.add_0_l;
    repeat rewrite Z.add_assoc;
    reflexivity.

Lemma inner_M_fix_0 : forall j b a00,
  0 <= j < 16 ->
  Zlength b = 16 ->
inner_M_fix 0 j a00 b
  (update_M_i_j 0 j a00 b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0]) =
upd_Znth j
  (inner_M_fix 0 j a00 b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
     0; 0; 0; 0; 0; 0; 0])
  (Znth j
     (inner_M_fix 0 j a00 b
        [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
        0; 0; 0; 0; 0; 0; 0; 0]) 0 + a00 * Znth j b 0).
Proof.
  intros j b v Hj Hb.
  rewrite Zlength_correct in Hb.
  assert(Hb' : (length b = 16)%nat) by go.
  repeat (destruct b ; tryfalse).
  rewrite <- Zlength_correct in *.
  (* all this following steps should be handled by reflection *)
  gen_i H j ; Grind_add_Z;
  repeat orewrite inner_M_i_j_eq;
  repeat orewrite Znth_nth;
  unfold nat_of_Z;
  change_Z_to_nat;
  simpl;
  unfold update_M_i_j';
  unfold local_update_M; simpl; 
  repeat orewrite upd_Znth_upd_nth;
  simpl;
  unfold update_M_i_j;
  change_Z_to_nat;
  unfold local_update_M; simpl;
  reify; apply decide_impl; vm_compute; auto.
Qed.

Close Scope Z.
