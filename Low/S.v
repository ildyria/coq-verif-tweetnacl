Require Import Tweetnacl.Libs.Export.
Require Export Tweetnacl.Low.M.

Definition Sq (a : list Z) : list Z := M a a.

Lemma Sq_length : forall a,
  length a = 16 ->
  length (Sq a) = 16.
Proof. intros; rewrite /Sq M_length ; omega. Qed.

Open Scope Z.

Lemma Sq_Zlength : forall a,
  Zlength a = 16 ->
  Zlength (Sq a) = 16.
Proof. Proof. intros; rewrite /Sq M_Zlength ; omega. Qed.

Close Scope Z.