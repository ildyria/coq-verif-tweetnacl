Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.Inv25519_gen.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl.Mid.Inv25519.
Require Import ssreflect.

Open Scope Z.

(*
 * Define the iteration step over Lists
 *)
Definition step_pow := step_pow Low.M Low.S.

(*
 * Equivalence over GF.
 *)
Local Lemma step_pow_Z_GF_eq: forall a c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  ZofList 16 (step_pow a c g) :𝓖𝓕  = (step_pow_Z a (ZofList 16 c) (ZofList 16 g)) :𝓖𝓕 .
Proof.
intros.
rewrite /step_pow /Inv25519_gen.step_pow /step_pow_Z.
flatten;
rewrite /step_pow /Low.S mult_GF_Zlengh => //.
rewrite Zmult_mod mult_GF_Zlengh -?Zmult_mod => //.
apply M_Zlength => //.
Qed.

(*
 * Define the recursion over list
 *)
Definition pow_fn_rev := pow_fn_rev Low.M Low.S.

Lemma pow_fn_rev_0 : forall b c g,
  pow_fn_rev 0 b c g = c.
Proof. go. Qed.

Lemma pow_fn_rev_n : forall a b c g,
  0 < a ->
  pow_fn_rev a b c g = step_pow (b -1 - a) (pow_fn_rev (a - 1) b c g) g.
Proof. intros. rewrite /pow_fn_rev pow_fn_rev_equation /step_pow; flatten; apply Zle_bool_imp_le in Eq; omega. Qed.

Lemma step_pow_Zlength : forall a c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Zlength (step_pow a c g) = 16.
Proof. apply step_pow_Zlength; [apply M_Zlength|apply Sq_Zlength]. Qed.

Lemma pow_fn_rev_Zlength : forall a b c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Zlength (pow_fn_rev a b c g) = 16.
Proof.  apply pow_fn_rev_Zlength; [apply M_Zlength|apply Sq_Zlength]. Qed.

Lemma pow_fn_rev_Z_GF : forall a b c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  ZofList 16 (pow_fn_rev a b c g) :𝓖𝓕  = (pow_fn_rev_Z a b (ZofList 16 c) (ZofList 16 g)) :𝓖𝓕 .
Proof.
  intros.
  destruct a; intros ; [go | | go].
  remember (Z.pos p) as a.
  assert(0 <= a) by (subst; apply Zle_0_pos).
  clears p.
  gen b c g.
  gen a.
  apply (natlike_ind (fun a => forall (b : ℤ) (c : list ℤ),
  Zlength c = 16 ->
  forall g : list ℤ,
  Zlength g = 16 -> (ℤ16.lst pow_fn_rev a b c g) :𝓖𝓕 = pow_fn_rev_Z a b (ℤ16.lst c) (ℤ16.lst g) :𝓖𝓕)).
  intros ; go.
  intros a Ha IHa b c Hc g Hg.
  change (Z.succ a) with (a + 1).
  orewrite pow_fn_rev_Z_n.
  orewrite pow_fn_rev_n.
  oreplace (a + 1 - 1) a.
  rewrite step_pow_Z_GF_eq /step_pow_Z => //.
  2: apply pow_fn_rev_Zlength => //.
  flatten.
  rewrite Zmult_assoc_reverse Zmult_mod.
  symmetry.
  rewrite Zmult_assoc_reverse Zmult_mod IHa => //.
  f_equal.
  f_equal.
  rewrite Zmult_mod.
  symmetry.
  rewrite Zmult_mod IHa => //.
  rewrite Zmult_mod.
  symmetry.
  rewrite Zmult_mod.
  rewrite IHa => //.
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

(* Define Inv25519 *)

Definition Inv25519 (x:list Z) : (list Z) := pow_fn_rev 254 254 x x.

Lemma Inv25519_pow_fn_rev : forall p o,
  p = pow_fn_rev 254 254 o o -> p = Inv25519 o.
Proof. by rewrite /Inv25519. Qed.

Lemma Inv25519_bound_Zlength : forall g,
  Zlength g = 16 ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) g ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Inv25519 g).
Proof. intros; rewrite /Inv25519; apply pow_fn_rev_bound_Zlength => //. Qed.

Lemma Inv25519_Zlength : forall g,
  Zlength g = 16 ->
  Zlength (Inv25519 g) = 16.
Proof. intros; rewrite /Inv25519; apply pow_fn_rev_Zlength => //. Qed.

Lemma Inv25519_Z_GF : forall g,
  Zlength g = 16 ->
  ZofList 16 (Inv25519 g) :𝓖𝓕  = (Inv25519_Z (ZofList 16 g)) :𝓖𝓕 .
Proof. intros; rewrite /Inv25519 /Inv25519_Z; apply pow_fn_rev_Z_GF => //. Qed.

Corollary Inv25519_Zpow_GF : forall g,
  Zlength g = 16 ->
  ZofList 16 (Inv25519 g) :𝓖𝓕  = (Z.pow (ZofList 16 g) (Z.pow 2 255 - 21)) :𝓖𝓕 .
Proof. intros. rewrite Inv25519_Z_GF //.
f_equal. apply Inv25519_Z_correct. Qed.

Close Scope Z.
