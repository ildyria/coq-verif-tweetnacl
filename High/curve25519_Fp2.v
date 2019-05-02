Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import Zmodp2_rules.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Definition a : Zmodp2.type := Zmodp2.pi (Zmodp.pi 486662, 0).
Definition b : Zmodp2.type := Zmodp2.pi (1, 0).

Lemma b_neq0 : b != 0.
Proof. exact: oner_neq0. Qed.

Lemma asq_neq4 : (a ^+ 2 != 4%:R).
Proof.
rewrite expr2 /a.
change (Zmodp2.piZ (486662, 0%Z)) with (Zmodp2.pi (Zmodp.pi 486662, Zmodp.pi 0)).
rewrite Zmodp2_mulE /=.
apply/eqP => H.
inversion H ; clear H.
move/eqP: H1.
zmodp_compute.
move/eqP => H.
inversion H.
Qed.

Canonical Structure curve25519_Fp2_mcuType := Build_mcuType b_neq0 asq_neq4.

Lemma curve25519_Fp2_chi2 : 2%:R != 0 :> Zmodp2.type.
Proof.
simpl.
have -> : 2%:R = Zmodp2.one + Zmodp2.one :> Zmodp2.type by rewrite Zmodp2_addE.
apply Zmodp2_ring.two_neq_zero.
Qed.

Lemma curve25519_Fp2_chi3 : 3%:R != 0 :> Zmodp2.type.
Proof.
have -> : 3%:R = Zmodp2.one + Zmodp2.one + Zmodp2.one :> Zmodp2.type.
2: apply Zmodp2_ring.three_neq_zero.
by apply/eqP; zmodp2_compute; zmodp_compute; apply/andP; split; zmodp_compute.
Qed.

Definition curve25519_Fp2_ecuFieldMixin :=
  ECUFieldMixin curve25519_Fp2_chi2 curve25519_Fp2_chi3.
Canonical Structure curve25519_Fp2_ecuFieldType :=
  Eval hnf in ECUFieldType Zmodp2.type curve25519_Fp2_ecuFieldMixin.
Canonical Structure curve25519_Fp2_finECUFieldType :=
  Eval hnf in [finECUFieldType of Zmodp2.type].

Definition curve25519_Fp2_ladder n x :=
  @opt_montgomery curve25519_Fp2_finECUFieldType curve25519_Fp2_mcuType n 255 x.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Lemma oncurve_0_0: oncurve curve25519_Fp2_mcuType (|0%:R ,0%:R|).
Proof. move => /=. rewrite /b /a.
have -> : Zmodp2.pi (1,0) = 1%:R => //=.
Zmodpify => /= ; ringify => /= ; ring_simplify_this.
Qed.

Lemma oncurve_inf: oncurve curve25519_Fp2_mcuType ∞.
Proof. done. Qed.

Lemma p_x0_0_impl : forall p: mc curve25519_Fp2_mcuType,
  p #x0 = 0%:R ->
  p = MC oncurve_0_0 \/ p = MC oncurve_inf.
Proof.
  move => [] [p Hp|xp yp Hp] => /=.
  + by right ; apply mc_eq.
  + move => Hxp.
  left ; apply mc_eq.
  move: Hxp Hp -> => /=.
  rewrite /a /b.
  have -> : Zmodp2.pi (1,0) = 1%:R => //=.
  Zmodpify => /= ; ringify => /= ; ring_simplify_this.
  have ->: Zmodp2.Zmodp2 0 0 = 0%:R => //=.
  by rewrite mulf_eq0; move /orP => []/eqP ->.
Qed.

Lemma n_inf : forall n p,
  p = MC oncurve_inf -> 
  p *+ n = MC oncurve_inf.
Proof.
  move => n p.
  have ->: MC (M:=curve25519_Fp2_mcuType) (p:=∞) oncurve_inf = 0.
  by rewrite /0 => /= ; apply mc_eq.
  move => ->.
  apply mul0rn.
Qed.

Lemma eq_0_0_0_0_inf : forall x y z,
  x = MC oncurve_0_0 ->
  y = MC oncurve_0_0 ->
  z = MC oncurve_inf ->
  x + y = z.
Proof. by move => x y z -> -> ->; rewrite /GRing.add /= ; apply mc_eq. Qed.

Lemma eq_0_0_inf_0_0 : forall x y z,
  x = MC oncurve_0_0 ->
  y = MC oncurve_inf ->
  z = MC oncurve_0_0 ->
  x + y = z.
Proof. by move => x y z -> -> ->; rewrite /GRing.add /= ; apply mc_eq. Qed.

Lemma p_x0_0_eq_0 : forall (n:nat) (p: mc curve25519_Fp2_mcuType),
  p #x0 = 0%:R ->
  (p *+ n) #x0 = 0%R.
Proof.
  elim => [| n IHn] => p.
  move => _ ; rewrite mulr0n => //=.
  rewrite mulrS => Hp.
  have /IHn/p_x0_0_impl := Hp.
  move => [] ->.
  all: move/p_x0_0_impl:Hp.
  all: move => [] ->.
  all: rewrite /GRing.add //=.
Qed.


(*
Theorem curve25519_Fp2_ladder_ok (n : nat) (x : Zmodp.type) :
    (n < 2^255)%nat -> x != 0 ->
    forall (p : mc curve25519_Fp2_mcuType), p#x0 = Zmodp2.pi (x, Zmodp.zero) -> curve25519_Fp2_ladder n (Zmodp2.pi (x, Zmodp.zero)) = (p *+ n)#x0.
Proof.
move => Hn Hx p Hp.
rewrite /curve25519_Fp2_ladder.
apply opt_montgomery_ok=> //=.
2: by apply/eqP => H ; inversion H ; subst.
Admitted.
*)
(* apply curve25519_residute. *)
(* Qed. *)
