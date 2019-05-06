Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.

Require Import Ring.
Open Scope ring_scope.
Import GRing.Theory.
Import Zmodp2.
Import BinInt.

Lemma expr3 : forall x:Zmodp2.type, x^+3 = x*x*x :> Zmodp2.type.
Proof. move => x; rewrite ?exprSr expr0 GRing.mul1r //. Qed.

Lemma expr3' : forall x:Zmodp.type, (x^+3 = x*x*x)%R.
Proof. move => x; rewrite ?exprSr expr0 GRing.mul1r //. Qed.

Ltac ring_simplify_this :=
  repeat match goal with
  | _ => rewrite expr2
  | _ => rewrite expr3
  | _ => rewrite GRing.mul1r
  | _ => rewrite GRing.mulr1
  | _ => rewrite GRing.mul0r
  | _ => rewrite GRing.mulr0
  | _ => rewrite GRing.add0r
  | _ => rewrite GRing.oppr0
  | _ => rewrite GRing.addr0
  | _ => done
end.

Lemma pi_2 : Zmodp.pi 2 = 2%:R.
Proof. by apply/eqP ; zmodp_compute. Qed.

Ltac ringify := repeat match goal with
  | [ |- context[Zmodp.pi 2]] => rewrite pi_2
  | [ |- context[Zmodp.mul ?a ?b]] => have ->: (Zmodp.mul a b) = a * b => //
  | [ |- context[Zmodp.add ?a (Zmodp.opp ?b)]] => have ->: (Zmodp.add a (Zmodp.opp b)) = a - b => //
  | [ |- context[Zmodp.opp ?a]] => have ->: Zmodp.opp a = -a => //
  | [ |- context[Zmodp.add ?a ?b]] => have ->: (Zmodp.add a b) = a + b => //
  | [ |- context[Zmodp2.mul ?a ?b]] => have ->: (Zmodp2.mul a b) = a * b => //
  | [ |- context[Zmodp2.add ?a ?b]] => have ->: (Zmodp2.add a b) = a + b => //
  | [ |- context[Zmodp.one] ] => have ->: Zmodp.one = 1 => //
  | [ |- context[Zmodp.zero] ] => have ->: Zmodp.zero = 0 => //
  end.

(*
 * Operations of the form (a , 0) op (b , 0)
 *)

Lemma Zmodp2_add_Zmodp_a0 a b: Zmodp2 a 0 + Zmodp2 b 0 = Zmodp2 (a + b) 0.
Proof.
  rewrite /GRing.add /= /add /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_opp_Zmodp_a0 a: - Zmodp2 a 0 = Zmodp2 (-a) 0.
Proof.
  rewrite /GRing.opp /= /opp /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_sub_Zmodp_a0 a b: Zmodp2 a 0 - Zmodp2 b 0 = Zmodp2 (a - b) 0.
Proof.
  rewrite /GRing.add /= /add /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_mul_Zmodp_a0 a b :Zmodp2 a 0 * Zmodp2 b 0 = Zmodp2 (a * b) 0.
Proof.
  rewrite /GRing.mul /= /mul /=.
  ringify ; ring_simplify_this.
Qed.

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
Proof.
  rewrite /GRing.add /= /add /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_opp_Zmodp_0a a: - Zmodp2 0 a = Zmodp2 0 (-a).
Proof.
  rewrite /GRing.opp /= /opp /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_sub_Zmodp_0a a b: Zmodp2 0 a - Zmodp2 0 b = Zmodp2 0 (a - b).
Proof.
  rewrite /GRing.add /= /add /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_mul_Zmodp_0a a b: Zmodp2 0 a * Zmodp2 0 b = Zmodp2  (2%:R * a * b) 0.
Proof.
  rewrite /GRing.mul /= /mul /=.
  ringify ; ring_simplify_this.
  by rewrite GRing.mulrA.
Qed.


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
Proof.
  rewrite /GRing.mul /= /mul /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_mul_Zmodp_ab2 a b: Zmodp2 0 a * Zmodp2 b 0 = Zmodp2 0 (a * b).
Proof.
  rewrite /GRing.mul /= /mul /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp_mul_comm_2 (a:Zmodp.type) : 2%:R * a = a * 2%:R.
Proof. by rewrite /GRing.mul /= Zmodp_ring.mul_comm. Qed.












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
