Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import GRing_tools.

Require Import Ring.
Open Scope ring_scope.
Import GRing.Theory.
Import Zmodp2.
Import BinInt.

Local Ltac unfolds := ring_unfold; Zmodp2_unfold.

Ltac ringify := Zmodp_ringify ; Zmodp2_ringify.

Ltac do_ := unfolds ; ringify ; ring_simplify_this.

(*
 * Operations of the form (a , 0) op (b , 0)
 *)

Lemma Zmodp2_add_Zmodp_a0 a b: Zmodp2 a 0 + Zmodp2 b 0 = Zmodp2 (a + b) 0.
Proof. do_. Qed.

Lemma Zmodp2_opp_Zmodp_a0 a: - Zmodp2 a 0 = Zmodp2 (-a) 0.
Proof. do_. Qed.

Lemma Zmodp2_sub_Zmodp_a0 a b: Zmodp2 a 0 - Zmodp2 b 0 = Zmodp2 (a - b) 0.
Proof. do_. Qed.

Lemma Zmodp2_mul_Zmodp_a0 a b :Zmodp2 a 0 * Zmodp2 b 0 = Zmodp2 (a * b) 0.
Proof. do_. Qed.

Lemma Zmodp2_pow_Zmodp_a0 : forall n a, (Zmodp2 a 0) ^+ n = Zmodp2 (a^+n) 0.
Proof.
  elim => [| n IHn] a.
  - by rewrite ?expr0.
  - by rewrite ?exprS IHn Zmodp2_mul_Zmodp_a0.
Qed.

Lemma Zmodp2_inv_Zmodp_a0 a :(Zmodp2 a 0)^-1 = Zmodp2 (a^-1) 0.
Proof.
have/orP := orbN (Zmodp.eqb a 0).
move => []; move/Refl.eqb_spec.
- by move => ->; rewrite ?invr0.
- move => Ha.
apply GRing.mulr1_eq.
rewrite Zmodp2_mul_Zmodp_a0 GRing.mulfV //.
by apply/eqP.
Qed.

(*
 * Operations of the form (a , 0) op (b , 0)
 *)
Lemma Zmodp2_add_Zmodp_0a a b: Zmodp2 0 a + Zmodp2 0 b = Zmodp2 0 (a + b).
Proof. do_. Qed.

Lemma Zmodp2_opp_Zmodp_0a a: - Zmodp2 0 a = Zmodp2 0 (-a).
Proof. do_. Qed.

Lemma Zmodp2_sub_Zmodp_0a a b: Zmodp2 0 a - Zmodp2 0 b = Zmodp2 0 (a - b).
Proof. do_. Qed.

Lemma Zmodp2_mul_Zmodp_0a a b: Zmodp2 0 a * Zmodp2 0 b = Zmodp2  (2%:R * a * b) 0.
Proof. by do_; rewrite GRing.mulrA. Qed.

Lemma Zmodp2_inv_Zmodp_0a a :(Zmodp2 0 a)^-1 = Zmodp2 0 ((2%:R * a)^-1).
Proof.
have/orP := orbN (Zmodp.eqb a 0).
move => []; move/Refl.eqb_spec.
- by move => -> ; rewrite GRing.mulr0 ?invr0.
- move => Ha.
  apply GRing.mulr1_eq.
  rewrite Zmodp2_mul_Zmodp_0a GRing.mulfV //.
  apply/eqP => H2a.
  apply: Ha.
  move: H2a.
  apply time_2_eq_0.
Qed.

(*
 * Operations of the form (a , 0) op (0 , b)
 *)


Lemma Zmodp2_mul_Zmodp_ab1 a b: Zmodp2 a 0 * Zmodp2 0 b = Zmodp2 0 (a * b).
Proof. do_. Qed.

Lemma Zmodp2_mul_Zmodp_ab2 a b: Zmodp2 0 a * Zmodp2 b 0 = Zmodp2 0 (a * b).
Proof. do_. Qed.

Lemma Zmodp_mul_comm_2 (a:Zmodp.type) : 2%:R * a = a * 2%:R.
Proof. by rewrite GRing.mulrC. Qed.

(*
 * Big rewrite tactic
 *)
Ltac Zmodpify := repeat match goal with 
  | _ => rewrite Zmodp2_add_Zmodp_a0
  | _ => rewrite Zmodp2_sub_Zmodp_a0
  | _ => rewrite Zmodp2_opp_Zmodp_a0
  | _ => rewrite Zmodp2_add_Zmodp_0a
  | _ => rewrite Zmodp2_sub_Zmodp_0a
  | _ => rewrite Zmodp2_opp_Zmodp_0a
  | _ => rewrite Zmodp2_mul_Zmodp_a0
  | _ => rewrite Zmodp2_pow_Zmodp_a0
  | _ => rewrite Zmodp2_inv_Zmodp_a0
  | _ => rewrite Zmodp2_mul_Zmodp_0a
  | _ => rewrite Zmodp2_mul_Zmodp_ab1
  | _ => rewrite Zmodp2_mul_Zmodp_ab2
  | _ => rewrite Zmodp2_inv_Zmodp_0a
end.
