Require Import Tweetnacl.Libs.Export.
Require Export Tweetnacl.Low.M.
Require Import ssreflect.

Module Low.

Definition S (a : list Z) : list Z := Low.M a a.

End Low.

Lemma Sq_length : forall a,
  length a = 16 ->
  length (Low.S a) = 16.
Proof. intros; rewrite /Low.S M_length ; omega. Qed.

Open Scope Z.

Lemma Sq_Zlength : forall a,
  Zlength a = 16 ->
  Zlength (Low.S a) = 16.
Proof. intros; rewrite /Low.S M_Zlength ; omega. Qed.

Lemma Sq_bound_length : forall a,
  (length a = 16)%nat ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Low.S a).
Proof. intros; rewrite /Low.S ; apply M_bound_length; go. Qed.

Lemma Sq_bound_Zlength : forall a,
  Zlength a = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Low.S a).
Proof. intros; rewrite /Low.S ; apply M_bound_Zlength; go. Qed.

Close Scope Z.