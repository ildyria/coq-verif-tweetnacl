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
From Tweetnacl.High Require Import curve_incl_Fp2.
From Tweetnacl.High Require Import twist_incl_Fp2.
From Tweetnacl.High Require Import Zmodp.
Require Import Ring.
Require Import ZArith.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "Z.R A" := (Zmodp.repr A) (at level 30).
Local Notation "-. A" := (Zmodp.opp A) (at level 30).

Lemma oncurve_inf : oncurve curve25519_Fp2_mcuType (EC_Inf Zmodp2.type).
Proof. done. Defined.

Local Lemma oncurve_00 : (oncurve curve25519_Fp2_mcuType (EC_In 0 0)).
Proof.
  simpl; rewrite /a /b ; apply/eqP.
  have ->: (0 ^+ 2)%R = 0 :> Zmodp2.type by ring_simplify_this.
  have ->: (0 ^+ 3)%R = 0 :> Zmodp2.type by ring_simplify_this.
  rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
  f_equal; f_equal; apply/eqP ; zmodp_compute => //=.
Qed.

Local Lemma oncurve25519 : forall x k k0 : Zmodp.type,
curve25519.b * k0 ^+ 2 == k ^+ 3 + curve25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have : oncurve curve25519_mcuType (EC_In k k') => //.
move/oncurve25519_impl => HOC.
exists (MC HOC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Local Lemma ontwist25519 : forall x k k0 : Zmodp.type,
twist25519.b * k0 ^+ 2 == k ^+ 3 + twist25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have : oncurve twist25519_mcuType (EC_In k k') => //.
move/ontwist25519_impl => HOC.
exists (MC HOC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

(* May actually not be in the right direction... *)
Theorem x_is_on_curve_or_twist_implies_x_in_Fp2: forall (x:Zmodp.type),
  exists (p: mc curve25519_Fp2_mcuType), p#x0 = Zmodp2.Zmodp2 x 0.
Proof.
  move=> x.
  have := x_is_on_curve_or_twist x.
  move=> [] [] [] [] /=.
  - move=> _ <- ; exists (MC oncurve_00) => //=.
  - apply oncurve25519.
  - move=> _ <- ; exists (MC oncurve_00) => //=.
  - apply ontwist25519.
Qed.

Definition Fp_to_Fp2 p := match p with
  | Zmodp2.Zmodp2 x y => x
  end.

Lemma Fp_to_Fp2_t : forall p:mc twist25519_mcuType,
  p#x0 = Fp_to_Fp2 ((twist25519_Fp_to_Fp2 p)#x0).
Proof. by case; case. Qed.

Lemma Fp_to_Fp2_c : forall p:mc curve25519_mcuType,
  p#x0 = Fp_to_Fp2 ((curve25519_Fp_to_Fp2 p)#x0).
Proof. by case; case. Qed.

Lemma Fp_to_Fp2_eq_C: Fp_to_Fp2 = cFp_to_Fp2.
Proof. reflexivity. Qed.

Lemma Fp_to_Fp2_eq_T: Fp_to_Fp2 = tFp_to_Fp2.
Proof. reflexivity. Qed.

From mathcomp Require Import ssrnat.
Local Notation "p '/p'" := (Fp_to_Fp2 p) (at level 40).

Lemma curve25519_ladder_maybe_ok (n : nat) x :
    (n < 2^255)%nat -> x != 0 ->
    forall (p'  : mc curve25519_Fp2_mcuType),
    (exists p, curve25519_Fp_to_Fp2 p #x0 /p = x) \/ (exists p, twist25519_Fp_to_Fp2 p #x0 /p = x) ->
    p'#x0 /p = x -> curve25519_ladder n x = (p' *+ n)#x0 /p.
Proof.
  move => Hn Hx p' [[p Hp]|[p Hp]] Hp'.
(*   have [[p Hp]|[p Hp]]:= x_is_on_curve_or_twist x. *)
  rewrite (curve25519_ladder_really_ok n x Hn Hx p Hp) -Fp_to_Fp2_eq_C.
  f_equal.
  f_equal.
  f_equal.
  f_equal.
  destruct p, p' => /=.
  apply mc_eq.
  destruct p, p0 => //=.
  move: Hp Hp' Hx => /= <- //=.
  move: Hp Hp' Hx => /= <- <- //=.
  move: Hp Hp' => /= -> <-.
Admitted.

Theorem curve25519_ladder_really_ok (n : nat) (x:Zmodp.type) :
    (n < 2^255)%nat -> x != 0 ->
    forall (p'  : mc curve25519_Fp2_mcuType),
    p'#x0 /p = x -> curve25519_ladder n x = (p' *+ n)#x0 /p.
Proof.
  have : (exists p, curve25519_Fp_to_Fp2 p #x0 /p = x) \/ (exists p, twist25519_Fp_to_Fp2 p #x0 /p = x).
  have := (x_is_on_curve_or_twist x).
  move => [[p Hp]|[p Hp]].
  by left; exists p;  move: p Hp => [[| xp yp] Hp] /=.
  by right; exists p;  move: p Hp => [[| xp yp] Hp] /=.
  intros ; apply curve25519_ladder_maybe_ok => //.
Qed.


Close Scope ring_scope.
