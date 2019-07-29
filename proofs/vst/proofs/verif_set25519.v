Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_set25519.
Require Import Tweetnacl.Libs.Export.

Open Scope Z.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
      ltac:(with_library prog [set25519_spec]).

Lemma body_set25519: semax_body Vprog Gprog f_set25519 set25519_spec.
Proof.
start_function.
forward_for_simple_bound 16 (set25519_Inv shr sha r a contents_r contents_a).
- entailer!.
- assert(Haux1: exists aux1, Vlong aux1 = Znth i (mVI64 contents_a) Vundef).
  { 
  erewrite (Znth_map Int64.zero).
  eexists ; reflexivity.
  rewrite Zlength_map ; go.
  }
  destruct Haux1 as [aux1 Haux1].
  forward ; rewrite <- Haux1.
  entailer!.
  forward. entailer!.
  clean_context_from_VST.
  replace_cancel.
  rewrite Haux1.
  rewrite (Znth_map Int64.zero).
  2: rewrite Zlength_map; go.
  rewrite -(Znth_map _ _ _ _ _ (Vlong Int64.zero)).
  2: rewrite Zlength_map; go.
  replace (nat_of_Z (i + 1)) with (S (nat_of_Z i)) by 
    (rewrite nat_of_Z_plus ; try omega; change (nat_of_Z 1) with 1%nat ; omega).

  assert(Z.of_nat (nat_of_Z i) < 16).
  rewrite Z2Nat.id ; omega.

  erewrite upd_Znth_app_step_Zlength ; eauto.
  omega.
  omega.
  rewrite ?Zlength_map ; omega.

  - forward.
  clean_context_from_VST.
  rewrite list.take_ge.
  rewrite list.drop_ge.
  rewrite app_nil_r.
  cancel.
  rewrite Nat2Z.inj_le.
  rewrite <- Zlength_correct.
  change (Z.of_nat (Pos.to_nat 16)) with 16.
  omega.

  rewrite Nat2Z.inj_le -Zlength_correct.
  change (Z.of_nat (Pos.to_nat 16)) with 16.
  go.
Qed.

Close Scope Z.