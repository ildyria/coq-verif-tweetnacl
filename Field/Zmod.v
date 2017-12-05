Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype seq ssrfun ssrnat ssralg ssrint.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.A.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope Z.

(* EqType for Z TODO: move to another file *)
Lemma Z_eqP : Equality.axiom Z.eqb.
Proof. by move=> x y; apply: (equivP idP); exact: Z.eqb_eq. Qed.
Definition Z_eqMixin := Equality.Mixin Z_eqP.
Canonical Structure Z_eqType := EqType Z Z_eqMixin.

Module Zlist16.

Inductive Zlist16 : Set := ZList16 (l : list Z) of length l == 16%N.
Coercion list_of_Zlist16 l := let: ZList16 l _ := l in l.

Canonical Structure subType := [subType for list_of_Zlist16].
Definition eqMixin := Eval hnf in [eqMixin of Zlist16 by <:].
Canonical Structure eqType := EqType Zlist16 eqMixin.

Lemma len_eq_16 (x : Zlist16) : length (val x) = 16%N.
Proof. by apply/eqP; exact: (valP x). Qed.

Lemma add_ok x y : length x = 16%N -> length y = 16%N -> length (A x y) == 16%N.
Proof. by move=> Hx Hy; apply/eqP; apply: A_length. Qed.

Definition zero : Zlist16 := Sub (nseq 16 0) erefl.
Definition add (x y : Zlist16) : Zlist16 := Sub (A x y) (add_ok (len_eq_16 x) (len_eq_16 y)).

Lemma add_left_id : left_id zero add.
Proof.
move=> x.
apply/eqP; rewrite eqE; apply/eqP.
case: x.
by do 16!case=> // ?.
Qed.

Lemma add_associative : associative add.
Proof.
move=> x y z.
apply/eqP; rewrite eqE /= eq_sym; apply/eqP.
by exact: ZsumList_assoc.
Qed.

Lemma add_commutative : commutative add.
Proof.
move=> x y.
apply/eqP; rewrite eqE /=; apply/eqP.
by exact: ZsumList_comm.
Qed.

End Zlist16.