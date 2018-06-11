Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import montgomery_step_gen.
From Tweetnacl.Gen Require Import montgomery_rec.
From Tweetnacl.Gen Require Import step_gen.
From Tweetnacl.Gen Require Import abstract_rec.
From Tweetnacl.Gen Require Import abstract_rec_rev.
From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import abstract_rec_rev_eq.

Open Scope Z.

Section Montgomery_Rec_Eq.

Context {T : Type}.
Context {T' : Type}.
Context {O : Ops T T'}.

Theorem montgomery_rec_eq: forall n z a b c d e f x,
  montgomery_rec n z a b c d e f x =
  abstract_rec n z a b c d e f x.
Proof.
induction n ; intros.
reflexivity.
simpl.
apply IHn.
Qed.

Theorem montgomery_rec_eq_rev: forall n z a b c d e f x,
  montgomery_rec (S n) z a b c d e f x =
  abstract_rec_rev (S n) n z a b c d e f x.
Proof.
intros.
rewrite montgomery_rec_eq.
rewrite abstract_rec_equiv_rec_fn.
rewrite abstract_rec_rev_equiv_rec_fn_S_n.
apply Tail_Head_equiv.
Qed.

Theorem montgomery_rec_eq_fn_rev: forall n z a b c d e f x,
  0 <= n ->
  montgomery_rec (S (Z.to_nat n)) z a b c d e f x =
  abstract_fn_rev (n + 1) n z a b c d e f x.
Proof.
intros.
rewrite montgomery_rec_eq_rev.
replace (S (Z.to_nat n)) with (Z.to_nat (n + 1)).
2: rewrite -Z2Nat.inj_succ ; change (Z.succ n) with (n + 1).
rewrite abstract_fn_rev_eq.
reflexivity.
all: omega.
Qed.

End Montgomery_Rec_Eq.

Close Scope Z.