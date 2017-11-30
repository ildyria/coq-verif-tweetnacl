Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Inv25519_gen.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.

Open Scope Z.

Definition step_pow := step_pow M Sq.

Definition pow_fn_rev := pow_fn_rev M Sq.

Lemma pow_fn_rev_0 : forall b c g,
  pow_fn_rev 0 b c g = c.
Proof. go. Qed.

Lemma pow_fn_rev_n : forall a b c g,
  0 < a ->
  pow_fn_rev a b c g = step_pow (b - a - 1) (pow_fn_rev (a - 1) b c g) g.
Proof. intros. rewrite /pow_fn_rev pow_fn_rev_equation /step_pow.
flatten; apply Zle_bool_imp_le in Eq; omega.
Qed.

Lemma step_pow_Zlength : forall a c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Zlength (step_pow a c g) = 16.
Proof. apply step_pow_Zlength.
apply M_Zlength.
apply Sq_Zlength.
Qed.

Lemma pow_fn_rev_Zlength : forall a b c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Zlength (pow_fn_rev a b c g) = 16.
Proof.
apply pow_fn_rev_Zlength.
apply M_Zlength.
apply Sq_Zlength.
Qed.

Lemma step_pow_bound_Zlength : forall a c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) g ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (step_pow a c g).
Proof.
  apply step_pow_bound_Zlength.
  apply Sq_Zlength.
  apply M_bound_Zlength.
  apply Sq_bound_Zlength.
Qed.

Lemma pow_fn_rev_bound_Zlength : forall a b c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) g ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (pow_fn_rev a b c g).
Proof.
  apply pow_fn_rev_bound_Zlength.
  apply M_Zlength.
  apply Sq_Zlength.
  apply M_bound_Zlength.
  apply Sq_bound_Zlength.
Qed.

Close Scope Z.
