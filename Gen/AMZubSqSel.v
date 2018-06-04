Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
(* Require Import Tweetnacl.Low.Car25519.
Require Import Tweetnacl.Mid.Reduce. *)

Open Scope Z.

Class Ops (T: Type) :=
{
  A : T -> T -> T;
  M : T -> T -> T;
  Zub : T -> T -> T;
  Sq : T -> T;
  _121665: T;
  Sel25519 : Z -> T -> T -> T;
  getbit : Z -> T -> Z;
}.

Close Scope Z.