Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Export Mid.SumList.

(* Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZsumList_correct_impl : forall a b o, a ⊕ b = o -> (ℤ.lst a) + (ℤ.lst b) = ℤ.lst o.
Proof.
 *)