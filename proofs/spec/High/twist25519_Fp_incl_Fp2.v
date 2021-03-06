Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import twist25519_Fp.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import Zmodp2_rules.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_Fp_twist25519_Fp_eq.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import GRing_tools.
Require Import Ring.
Require Import ZArith.

Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

(* Conversion between twist25519 over F_p and F_p2 *)
Definition twist_Fp_to_Fp2 (p: point Zmodp.type) : (point Zmodp2.type) :=
match p with
  | EC_Inf => EC_Inf Zmodp2.type
  | EC_In x y => EC_In (Zmodp2.Zmodp2 x 0) (Zmodp2.Zmodp2 0 y)
end.

Lemma ontwist25519_Fp_impl : forall (x y: Zmodp.type),
oncurve twist25519_Fp_mcuType (EC_In x y) ->
(oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (x, Zmodp.pi 0)) (Zmodp2.pi (Zmodp.pi 0, y)))).
Proof.
move => x y /=.
rewrite /a /b.
ring_simplify_this.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
rewrite /twist25519_Fp.a /twist25519_Fp.b.
ring_simplify_this.
move/eqP => -> /=.
apply eq_refl.
Qed.

Local Lemma on_twist_Fp_to_Fp2 : forall (p: point Zmodp.type),
  oncurve twist25519_Fp_mcuType p -> oncurve curve25519_Fp2_mcuType (twist_Fp_to_Fp2 p).
Proof.
  move=> [|x y] => //.
  apply ontwist25519_Fp_impl.
Qed.

Definition twist25519_Fp_to_Fp2 (p: mc twist25519_Fp_mcuType) : (mc curve25519_Fp2_mcuType) :=
match p with
  | MC u P => MC (on_twist_Fp_to_Fp2 u P)
end.

Local Lemma twist_add_Fp_to_Fp2 : forall (p q: point Zmodp_ringType) (p' q': point Zmodp2_ringType),
  p' = twist_Fp_to_Fp2 p ->
  q' = twist_Fp_to_Fp2 q ->
  MCGroup.add curve25519_Fp2_mcuType p' q' = twist_Fp_to_Fp2 (MCGroup.add twist25519_Fp_mcuType p q).
Proof.
  move => [|xp yp] [|xq yq] [|xp' yp'] [|xq' yq'] //= [] -> -> [] -> ->.
  rewrite /twist25519_Fp.a /twist25519_Fp.b.
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
  subst Freezer.
  ringify.
  ring_simplify_this.
  case_eq (xp == xq) => -> ; rewrite -Zmodp_mul_comm_2 ?GRing.mulrA //=.
  case_eq ((yp == yq) && (yp != 0)) => -> //=.
Qed.

Local Lemma twist25519_add_Fp_to_Fp2_ : forall (p q: mc twist25519_Fp_mcuType) (p' q': mc curve25519_Fp2_mcuType),
  p' = twist25519_Fp_to_Fp2 p ->
  q' = twist25519_Fp_to_Fp2 q ->
  MCGroup.add curve25519_Fp2_mcuType p' q' = twist_Fp_to_Fp2 (MCGroup.add twist25519_Fp_mcuType p q).
Proof.
  move => [p Hp] [q Hq] [p' Hp'] [q' Hq'] Hpp' Hqq'.
  apply twist_add_Fp_to_Fp2.
  by simpl in Hpp'; inversion Hpp'.
  by simpl in Hqq'; inversion Hqq'.
Qed.

Local Lemma twist25519_add_Fp_to_Fp2: forall (p q: mc twist25519_Fp_mcuType),
  twist25519_Fp_to_Fp2 p + twist25519_Fp_to_Fp2 q = twist25519_Fp_to_Fp2 (p + q).
Proof.
  move => p q.
  have [p' Hp']: exists (p': mc curve25519_Fp2_mcuType), p' = twist25519_Fp_to_Fp2 p by exists (twist25519_Fp_to_Fp2 p).
  have [q' Hq']: exists (q': mc curve25519_Fp2_mcuType), q' = twist25519_Fp_to_Fp2 q by exists (twist25519_Fp_to_Fp2 q).
  ring_unfold.
  apply mc_eq.
  rewrite -(twist25519_add_Fp_to_Fp2_ _ _ _ _ Hp' Hq') Hp' Hq'.
  reflexivity.
Qed.

Lemma nP_is_nP2 : forall (n:nat) (p: mc twist25519_Fp_mcuType),
  twist25519_Fp_to_Fp2 (p *+ n) = (twist25519_Fp_to_Fp2 p) *+n.
Proof.
  elim => [|n IHn] p.
  ring_simplify_this.
  exact: mc_eq.
  by rewrite ?GRing.mulrS -IHn twist25519_add_Fp_to_Fp2.
Qed.

Definition tFp2_to_Fp p := match p with
  | Zmodp2.Zmodp2 x y => x
  end.

Lemma tFp2_to_Fp_cancel : forall (p: mc twist25519_Fp_mcuType),
  p#x0 = tFp2_to_Fp ((twist25519_Fp_to_Fp2 p)#x0).
Proof. by case; case. Qed.

Local Notation "p '/p'" := (tFp2_to_Fp p) (at level 40).

From mathcomp Require Import ssrnat.

Theorem twist25519_ladder_Fp_Fp2 (n : nat) x :
    (n < 2^255)%nat ->
    forall (p  : mc twist25519_Fp_mcuType),
    twist25519_Fp_to_Fp2 p #x0 = Zmodp2.Zmodp2 x 0 ->
    twist25519_Fp_ladder n x = ((twist25519_Fp_to_Fp2 p) *+ n)#x0 /p.
Proof.
  move => Hn p Hp.
  have Hp' := tFp2_to_Fp_cancel p.
  have Hp'' : p #x0 = x.
    rewrite Hp' Hp //.
  rewrite (twist25519_Fp_ladder_ok n x Hn p Hp'').
  rewrite -nP_is_nP2.
  rewrite tFp2_to_Fp_cancel //.
Qed.

Close Scope ring_scope.