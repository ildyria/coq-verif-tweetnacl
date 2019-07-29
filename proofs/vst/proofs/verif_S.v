Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_M.
Require Import Tweetnacl_verif.spec_S.

Open Scope Z.

Import Low.

Definition Gprog : funspecs := 
      ltac:(with_library prog [M_spec; S_spec]).

Lemma body_S: semax_body Vprog Gprog f_S S_spec.
Proof.
start_function.
unfold nm_overlap_array_sep_2.
flatten ; Intros.
1: subst o v_a.
1: forward_call (v_o,v_o,v_o,sho,sho,sho,(mVI64 a),a,a,3).
1: unfold_nm_overlap_array_sep; simpl; entailer!.
1: repeat match goal with | [ |- _ /\ _ ] => split; auto end.
2: forward_call (v_o,v_a,v_a,sho,sha,sha,o,a,a,2).
2: unfold_nm_overlap_array_sep; simpl; entailer!.
2: repeat match goal with | [ |- _ /\ _ ] => split; auto end.
all: unfold_nm_overlap_array_sep ; simpl.
all: forward.
all: unfold_nm_overlap_array_sep.
all: unfold S.
all: rewrite Eq.
all: entailer!.
all: apply M_Zlength ; assumption.
Qed.

Close Scope Z.