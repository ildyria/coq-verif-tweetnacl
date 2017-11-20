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

Lemma M_bound_length : forall a b,
  (length a = 16)%nat ->
  (length b = 16)%nat ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Proof.
intros. unfold M.
eapply Zcar25519_bounds_length_2 ; try reflexivity.
rewrite firstn_length.
orewrite M2_fix_length.
orewrite M1_fix_length.
reflexivity.
apply car25519_length.
rewrite firstn_length.
orewrite M2_fix_length.
orewrite M1_fix_length.
reflexivity.
eapply list.Forall_impl.
orewrite M2_fix_eq_M2.
2: orewrite M1_fix_length.
orewrite M1_fix_eq_M1.
eapply (mult_bound_le (-2 ^ 26) (2 ^ 26) (-2 ^ 26) (2 ^ 26)).
compute ; split ; intros; tryfalse.
compute ; split ; intros; tryfalse.
eapply list.Forall_impl ; eauto ; intros x Hx ; simpl in Hx; omega.
eapply list.Forall_impl ; eauto ; intros x Hx ; simpl in Hx; omega.
replace (Zlength a) with 16.
2: rewrite Zlength_correct; omega.
replace (Zlength b) with 16.
2: rewrite Zlength_correct; omega.
intros x Hx ; simpl in Hx.
rewrite Z.min_id in Hx.
change (min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (-2^52) in Hx.
change (max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (2^52) in Hx.
change (39 * 16 * - 2 ^ 52) with (-2810246167479189504) in Hx.
change (39 * 16 * 2 ^ 52) with (2810246167479189504) in Hx.
change (2^62) with              4611686018427387904.
change (-2^62) with           (-4611686018427387904).
omega.
Qed.

Lemma M_bound_Zlength : forall a b,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Proof. convert_length_to_Zlength M_bound_length. Qed.

Close Scope Z.