Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg finfield prime.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import curve25519_prime Zmodp prime_ssrprime.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope Z.

(* Import Zmodp. *)

Module Zmodp2.

(* Lemma prime_p : prime.prime (Z.to_nat p).
Proof. apply prime_ssrprime. rewrite Z_of_nat_to_nat_p /p -lock; apply primo. Qed.

Lemma pow2_pos : is_true (leq (S O) (S (S O))).
Proof. done. Qed.

Check sval.
Definition GFp2 := sval (PrimePowerField prime_p pow2_pos).
*)

Inductive type := Zmodp2 (x: Zmodp.type) (y:Zmodp.type).

Definition pi (x : Z*Z) : type := Zmodp2 (Zmodp.Zmodp (Zmodp.Z_mod_betweenb x.1 Hp_gt0)) (Zmodp.Zmodp (Zmodp.Z_mod_betweenb x.2 Hp_gt0)).
Coercion repr (x : type) : Z*Z := let: Zmodp2 (@Zmodp.Zmodp u _ ) (@Zmodp.Zmodp v _ ) := x in (u, v).

Variable d : Z.

Definition zero : type := pi (0,0).
Definition one : type := pi (1,0).
Definition opp (x : type) : type := pi (p - x.1 , p - x.2).
Definition add (x y : type) : type := pi (x.1 + y.1, x.2 + y.2).
Definition mul (x y : type) : type := pi (x.1 * y.1 + d * x.2 * y.2 , x.1 * y.2 + x.2 * y.1).

End Zmodp2.
Import Zmodp2.
(* 
Canonical Structure Zmodp2_subType := [subType for Zmodp2.repr].
Definition Zmodp2_eqMixin := Eval hnf in [eqMixin of Zmodp2.type by <:].
Canonical Structure Zmodp2_eqType := Eval hnf in EqType type Zmodp_eqMixin.
Definition Zmodp_choiceMixin := Eval hnf in [choiceMixin of type by <:].
Canonical Structure Zmodp_choiceType :=
  Eval hnf in ChoiceType type Zmodp_choiceMixin.
Definition Zmodp_countMixin := Eval hnf in [countMixin of type by <:].
Canonical Structure Zmodp_countType :=
  Eval hnf in CountType type Zmodp_countMixin.
 *)