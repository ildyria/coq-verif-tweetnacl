From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Mid Require Import Reduce.
From Tweetnacl.Mid Require Import GetBit.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Mid.AMZubSqSel.

From Tweetnacl.Gen Require Import abstract_rec_rev.

Require Import ssreflect.



Open Scope Z.

Local Instance Z_Ops : (Ops Z) := Build_Ops Z A Z.mul Z.sub (fun x => Z.mul x x) 121665 Sel25519 Zgetbit.

Definition Zmontgomery_Zabstract_rec := abstract_rec_rev.
Definition Zmontgomery_rec := abstract_rec.

(* Lemma Zabstract_eq_Zmontgomery_rec : forall n z a b c d e f x,
   Zmontgomery_rec n z a b c d e f x = Zmontgomery_Zabstract_rec n z a b c d e f x.
Proof.
  induction n ; intros.
  reflexivity.
  rewrite /Zmontgomery_rec in IHn.
  rewrite /Zmontgomery_rec opt_montgomery_rec_step_gen IHn.
  rewrite /Zmontgomery_Zabstract_rec.
  rewrite /Zmontgomery_step_gen /get_a /get_b /get_c /get_d /get_e /get_f.
  rewrite /Zabstract_rec.
  f_equal.
Qed.

Lemma Zmontgomery_fn_eq_rec : forall n z a b c d e f x,
   Zmontgomery_rec (S n) z a b c d e f x = Zmontgomery_fn (Z.of_nat (S n)) (Z.of_nat n) z a b c d e f x.
Proof.
Admitted.
 *)(*   intros.
  rewrite Zabstract_eq_Zmontgomery_rec.
  rewrite /Zmontgomery_Zabstract_rec.
  rewrite abstract_rec_equiv_rec_fn.
  rewrite /Zmontgomery_fn.
  induction n.
  reflexivity.
  rewrite /abstract_rec_fn.
  rewrite HeadTailRec.Tail_Head_equiv.
  rewrite Zabstract_fn_rev_equation.
  rewrite /HeadTailRec.rec_fn_rev.
  rewrite /HeadTailRec.rec_fn_rev_acc.
  

  rewrite /Zabstract_fn_rev.
  Search Zabstract_fn_rev. *)

Close Scope Z.