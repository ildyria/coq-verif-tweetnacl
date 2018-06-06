From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.abstract_fn_rev.
From Tweetnacl Require Import Gen.montgomery_rec.
From Tweetnacl Require Import Mid.AMZubSqSel.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Mid.GetBit.

Require Import ssreflect.

Open Scope Z.

Local Instance Z_Ops : (Ops Z) := Build_Ops Z A Z.mul Z.sub (fun x => Z.mul x x) 121665 Sel25519 Zgetbit.

Definition Zmontgomery_rec := montgomery_rec.
Definition Zmontgomery_fn := abstract_fn_rev.

Close Scope Z.