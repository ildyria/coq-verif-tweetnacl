Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
Require Import Tweetnacl.Low.Car25519.
Require Import Tweetnacl.Mid.Reduce.

Open Scope Z.

Definition A a b := Z.add a b.
Definition M a b := Zcar25519 (Zcar25519 (Z.mul a b)).
Definition Zub a b := Z.sub a b.
Definition Sq a := M a a.
Definition c_121665 := 121665.
Definition Sel25519 (b p q:Z) :=   if (Z.eqb b 0) then p else q.

Lemma A_bound_lt : forall m1 n1 m2 n2 a b,
  (fun x => m1 < x < n1) a -> 
  (fun x => m2 < x < n2) b -> 
  (fun x => m1 + m2 < x < n1 + n2) (A a b).
Proof. intros; simpl in *; rewrite /A; omega. Qed.

Lemma Zub_bound_lt : forall m1 n1 m2 n2 a b,
  (fun x => m1 < x < n1) a -> 
  (fun x => m2 < x < n2) b -> 
  (fun x => m1 - n2 < x < n1 - m2) (Zub a b).
Proof. intros; simpl in *; rewrite /Zub; omega. Qed.

Lemma M_bound : forall a b,
  (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Proof.
intros. unfold M.

Admitted.

Lemma Sq_bound : forall a,
  (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  (fun x => -38 <= x < Z.pow 2 16 + 38) (Sq a).
Proof. intros. unfold Sq. apply M_bound ; assumption. Qed.
