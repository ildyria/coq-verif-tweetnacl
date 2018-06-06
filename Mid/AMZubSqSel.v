Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Mid.Car25519.

Open Scope Z.

Definition A a b := Z.add a b.
Definition M a b := Zcar25519 (Zcar25519 (Z.mul a b)).
Definition Zub a b := Z.sub a b.
Definition Sq a := M a a.
Definition c_121665 := 121665.
Definition Sel25519 (b p q:Z) :=   if (Z.eqb b 0) then p else q.

Close Scope Z.