Require Import Tweetnacl.Libs.Export.
Require Export Tweetnacl.Low.M_low_level_compute.
Require Export Tweetnacl.Low.Inner_M1.
Require Export Tweetnacl.Low.Outer_M1.
Require Export Tweetnacl.Mid.M_low_level.
Require Export Tweetnacl.Mid.M.
Require Export Tweetnacl.Mid.ScalarMult.
Require Export Tweetnacl.Low.Car25519.
Require Export Tweetnacl.Mid.Car25519.

Definition M (a b : list Z) : list Z := (car25519 (car25519 (mult_3 
                  (M2_fix (Z.of_nat 15%nat)
                    (M1_fix a b)
                  )
                  ))).

Lemma M_length : forall a b, 
  length a = 16 ->
  length b = 16 -> 
  length (M a b) = 16.
Proof.
  intros.
  unfold M.
  apply car25519_length.
  apply car25519_length.
  unfold mult_3.
  rewrite firstn_length.
  orewrite M2_fix_length.
  orewrite M1_fix_length.
  reflexivity.
Qed.

Open Scope Z.

Lemma M_Zlength : forall a b, 
  Zlength a = 16 ->
  Zlength b = 16 -> 
  Zlength (M a b) = 16.
Proof. convert_length_to_Zlength M_length. Qed.

Close Scope Z.