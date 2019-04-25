Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.

Require Import Ring.
Open Scope ring_scope.
Import GRing.Theory.
Import Zmodp2.

Lemma expr3 : forall x:Zmodp2.type, x^+3 = x*x*x :> Zmodp2.type.
Proof.
move => x; rewrite ?exprSr expr0 GRing.mul1r //.
Qed.

Lemma expr3' : forall x:Zmodp.type, (x^+3 = x*x*x)%R.
Proof.
move => x; rewrite ?exprSr expr0 GRing.mul1r //.
Qed.


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

Ltac ringify := repeat match goal with
  | [ |- context[Zmodp.mul ?a ?b]] => have ->: (Zmodp.mul a b) = a * b => //
  | [ |- context[Zmodp.add ?a (Zmodp.opp ?b)]] => have ->: (Zmodp.add a (Zmodp.opp b)) = a - b => //
  | [ |- context[Zmodp.opp ?a]] => have ->: Zmodp.opp a = -a => //
  | [ |- context[Zmodp.add ?a ?b]] => have ->: (Zmodp.add a b) = a + b => //
  | [ |- context[Zmodp2.mul ?a ?b]] => have ->: (Zmodp2.mul a b) = a * b => //
  | [ |- context[Zmodp2.add ?a ?b]] => have ->: (Zmodp2.add a b) = a + b => //
  | [ |- context[Zmodp.one] ] => have ->: Zmodp.one = 1 => //
  | [ |- context[Zmodp.zero] ] => have ->: Zmodp.zero = 0 => //
  end.

Lemma Zmodp2_add_Zmodp a b: Zmodp2 a 0 + Zmodp2 b 0 = Zmodp2 (a + b) 0.
Proof.
  rewrite /GRing.add /= /add /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_opp_Zmodp a :- Zmodp2 a 0 = Zmodp2 (-a) 0.
Proof.
  rewrite /GRing.opp /= /opp /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_sub_Zmodp a b:Zmodp2 a 0 - Zmodp2 b 0 = Zmodp2 (a - b) 0.
Proof.
  rewrite /GRing.add /= /add /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_mul_Zmodp a b :Zmodp2 a 0 * Zmodp2 b 0 = Zmodp2 (a * b) 0.
Proof.
  rewrite /GRing.mul /= /mul /=.
  ringify ; ring_simplify_this.
Qed.

Lemma Zmodp2_pow_Zmodp : forall n a, (Zmodp2 a 0) ^+ n = Zmodp2 (a^+n) 0.
Proof.
  elim => [| n IHn] a.
  - by rewrite ?expr0.
  - by rewrite ?exprS IHn Zmodp2_mul_Zmodp.
Qed.

Lemma Zmodp2_inv_Zmodp a :(Zmodp2 a 0)^-1 = Zmodp2 (a^-1) 0.
Proof.
have/orP := orbN (Zmodp.eqb a 0).
move => []; move/Refl.eqb_spec.
- by move => ->; rewrite ?invr0.
- move => Ha.
apply GRing.mulr1_eq.
rewrite Zmodp2_mul_Zmodp GRing.mulfV //.
by apply/eqP.
Qed.

Lemma Zmodp2_div_Zmodp a b : (Zmodp2 a 0) / (Zmodp2 b 0) = Zmodp2 (a/b) 0.
Proof.
by rewrite Zmodp2_inv_Zmodp Zmodp2_mul_Zmodp.
Qed.

Ltac Zmodpify := repeat match goal with 
  | _ => rewrite Zmodp2_add_Zmodp
  | _ => rewrite Zmodp2_sub_Zmodp
  | _ => rewrite Zmodp2_opp_Zmodp
  | _ => rewrite Zmodp2_mul_Zmodp
  | _ => rewrite Zmodp2_pow_Zmodp
  | _ => rewrite Zmodp2_inv_Zmodp
  | _ => rewrite Zmodp2_div_Zmodp
end.
