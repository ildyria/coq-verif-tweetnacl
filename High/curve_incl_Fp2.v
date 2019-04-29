Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519.
From Tweetnacl.High Require Import twist25519.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import Zmodp2_rules.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_eq.
From Tweetnacl.High Require Import Zmodp.
Require Import Ring.
Require Import ZArith.

Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "Z.R A" := (Zmodp.repr A) (at level 30).
Local Notation "-. A" := (Zmodp.opp A) (at level 30).

(* Conversion between curve25519 over F_p and F_p2 *)
Definition curve_Fp_to_Fp2 (p: point Zmodp.type) : (point Zmodp2.type) :=
match p with
  | EC_Inf => EC_Inf Zmodp2.type
  | EC_In x y => EC_In (Zmodp2.Zmodp2 x 0) (Zmodp2.Zmodp2 y 0)
end.

Lemma oncurve25519_impl : forall (x y: Zmodp.type),
oncurve curve25519_mcuType (EC_In x y) ->
(oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (x, Zmodp.pi 0)) (Zmodp2.pi (y, Zmodp.pi 0)))).
Proof.
move => x y /=.
rewrite /a /b.
rewrite ?expr2 ?expr3 ?expr3'.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
rewrite /curve25519.a /curve25519.b.
ring_simplify_this.
move/eqP => -> /=.
apply/eqP.
f_equal.
Qed.

Lemma on_curve_Fp_to_Fp2 : forall (p: point Zmodp.type),
  oncurve curve25519_mcuType p -> oncurve curve25519_Fp2_mcuType (curve_Fp_to_Fp2 p).
Proof.
  move=> [|x y] => //.
  apply oncurve25519_impl.
Qed.

Definition curve25519_Fp_to_Fp2 (p: mc curve25519_mcuType) : (mc curve25519_Fp2_mcuType) :=
match p with
  | MC u P => MC (on_curve_Fp_to_Fp2 u P)
end.

Local Lemma curve_add_Fp_to_Fp2 : forall (p q: point Zmodp_ringType) (p' q': point Zmodp2_ringType),
  p' = curve_Fp_to_Fp2 p ->
  q' = curve_Fp_to_Fp2 q ->
  MCGroup.add curve25519_Fp2_mcuType p' q' = curve_Fp_to_Fp2 (MCGroup.add curve25519_mcuType p q).
Proof.
  move => [|xp yp] [|xq yq] [|xp' yp'] [|xq' yq'] //= [] -> -> [] -> ->.
  rewrite /curve25519.a /curve25519.b.
  match goal with
    | [ |- _ = ?A ] => remember A as Freezer
  end.
  rewrite /eq_op /Equality.op /=.
  rewrite /eq_op /Equality.op /=.
  rewrite !eq_refl ?Bool.andb_true_r.
  rewrite ?expr2.
  have ->: 2%:R = Zmodp2.Zmodp2 (2%:R) 0 => //.
  have ->: 3%:R = Zmodp2.Zmodp2 (3%:R) 0 => //.
  Zmodpify => /=.
  ringify.
  subst Freezer.
  ring_simplify_this.
  case_eq (xp == xq) => -> //=.
  case_eq ((yp == yq) && (yp != 0)) => -> //=.
Qed.

Local Lemma on_curve_add_Fp_to_Fp2 : forall (p q: point Zmodp_ringType),
  oncurve curve25519_mcuType p ->
  oncurve curve25519_mcuType q ->
   oncurve curve25519_Fp2_mcuType (curve_Fp_to_Fp2 (MCGroup.add curve25519_mcuType p q)).
Proof.
  move=> p q Hp Hq.
  pose p' := curve_Fp_to_Fp2 p.
  pose q' := curve_Fp_to_Fp2 q.
  rewrite -(curve_add_Fp_to_Fp2 p q p' q') => //.
  have OCp' : oncurve curve25519_Fp2_mcuType p' by subst p' ; apply on_curve_Fp_to_Fp2.
  have OCq' : oncurve curve25519_Fp2_mcuType q' by subst q' ; apply on_curve_Fp_to_Fp2.
  by apply MCGroup.addO'.
Qed.

Lemma on_curve25519_add_Fp_to_Fp2: forall (p q: mc curve25519_mcuType),
  oncurve curve25519_Fp2_mcuType (curve25519_Fp_to_Fp2 (p + q)).
Proof.
  by move => [p Hp] [q Hq] => /=; apply on_curve_add_Fp_to_Fp2.
Qed.


Local Lemma curve25519_add_Fp_to_Fp2' : forall (p q: mc curve25519_mcuType) (p' q': mc curve25519_Fp2_mcuType),
  p' = curve25519_Fp_to_Fp2 p ->
  q' = curve25519_Fp_to_Fp2 q ->
  MCGroup.add curve25519_Fp2_mcuType p' q' = curve_Fp_to_Fp2 (MCGroup.add curve25519_mcuType p q).
Proof.
  move => [p Hp] [q Hq] [p' Hp'] [q' Hq'] Hpp' Hqq'.
  apply curve_add_Fp_to_Fp2.
  by simpl in Hpp'; inversion Hpp'.
  by simpl in Hqq'; inversion Hqq'.
Qed.

Lemma curve25519_add_Fp_to_Fp2: forall (p q: mc curve25519_mcuType),
  curve25519_Fp_to_Fp2 p + curve25519_Fp_to_Fp2 q = curve25519_Fp_to_Fp2 (p + q).
Proof.
  move => p q.
  have [p' Hp']: exists (p': mc curve25519_Fp2_mcuType), p' = curve25519_Fp_to_Fp2 p by exists (curve25519_Fp_to_Fp2 p).
  have [q' Hq']: exists (q': mc curve25519_Fp2_mcuType), q' = curve25519_Fp_to_Fp2 q by exists (curve25519_Fp_to_Fp2 q).
  rewrite /GRing.add /=.
  apply mc_eq.
  rewrite -(curve25519_add_Fp_to_Fp2' _ _ _ _ Hp' Hq') Hp' Hq'.
  reflexivity.
Qed.

Lemma nP_is_nP2 : forall (n:nat) (p: mc curve25519_mcuType),
  curve25519_Fp_to_Fp2 (p *+ n) = (curve25519_Fp_to_Fp2 p) *+n.
Proof.
  elim => [|n IHn] p.
  rewrite ?GRing.mulr0n => /=.
  exact: mc_eq.
  by rewrite ?GRing.mulrS -IHn curve25519_add_Fp_to_Fp2.
Qed.

Definition cFp_to_Fp2 p := match p with
  | Zmodp2.Zmodp2 x y => x
  end.

Lemma cFp_to_Fp2_cancel : forall p: mc curve25519_mcuType,
  p#x0 = cFp_to_Fp2 ((curve25519_Fp_to_Fp2 p)#x0).
Proof. by case ; case. Qed.

Local Notation "p '/p'" := (cFp_to_Fp2 p) (at level 40).

From mathcomp Require Import ssrnat.

Theorem curve25519_ladder_really_ok (n : nat) x :
    (n < 2^255)%nat -> x != 0 ->
    forall (p  : mc curve25519_mcuType),
    (curve25519_Fp_to_Fp2 p)#x0 /p = x -> curve25519_ladder n x = ((curve25519_Fp_to_Fp2 p) *+ n)#x0 /p.
Proof.
  move => Hn Hx p Hp.
  have Hp' := cFp_to_Fp2_cancel p.
  have Hp'' : p #x0 = x.
  by rewrite Hp'.
  rewrite (curve25519_ladder_ok n x Hn Hx p Hp'').
  rewrite -nP_is_nP2.
  rewrite cFp_to_Fp2_cancel //.
Qed.

Close Scope ring_scope.