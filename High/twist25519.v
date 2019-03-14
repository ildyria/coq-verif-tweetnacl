Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Definition a : Zmodp.type := Zmodp.pi 486662.
Definition b : Zmodp.type := -1%R.

Lemma asq_neq4 : a^+2 != 4%:R.
Proof. by rewrite expr2; zmodp_compute. Qed.

Lemma b_neq0 : b != 0.
Proof. by rewrite /b; zmodp_compute. Qed.

Canonical Structure twist25519_mcuType := Build_mcuType b_neq0 asq_neq4.

Lemma twist25519_chi2 : 2%:R != 0 :> Zmodp.type.
Proof. by zmodp_compute. Qed.

Lemma twist25519_chi3 : 3%:R != 0 :> Zmodp.type.
Proof. by zmodp_compute. Qed.

Definition twist25519_ecuFieldMixin :=
  ECUFieldMixin twist25519_chi2 twist25519_chi3.
Canonical Structure twist25519_ecuFieldType :=
  Eval hnf in ECUFieldType Zmodp.type twist25519_ecuFieldMixin.
Canonical Structure twist25519_finECUFieldType :=
  Eval hnf in [finECUFieldType of Zmodp.type].

Lemma twist25519_residute (x : Zmodp.type) : x ^+ 2 != a ^+ 2 - 4%:R.
Proof.
replace (a ^+ 2 - 4%:R) with (Zmodp.pi 236839902240).
2: rewrite /a expr2 Zmodp_mulE /= Zmodp_oppE /= /Zmodp.p -lock /= Zmodp_addE //=.
have Prime:(Znumtheory.prime Zmodp.p).
  rewrite /Zmodp.p -lock ; apply curve25519_numtheory_prime.
have Prime2:= ZmodP_mod2_eq_1.
replace (BinInt.Z.sub (BinInt.Z.pow 2 255) 19) with Zmodp.p in Prime2.
2: rewrite /Zmodp.p -lock //.
have Eulers_Criterion := Eulers_criterion Zmodp.p Prime Prime2 (Zmodp.repr (Zmodp.pi 236839902240)).
rewrite /legendre in Eulers_Criterion.
destruct (ClassicalDescription.excluded_middle_informative _).
- rename e into H.
  exfalso.
  move: H.
  rewrite piK /p -lock //.
- destruct (ClassicalDescription.excluded_middle_informative _).
  + rename e into H.
    exfalso.
    move: Eulers_Criterion.
    rewrite piK /p.
    2: rewrite -lock //.
    replace (236839902240 ^ ((locked (2 ^ 255 - 19)%Z - 1) / 2) mod locked (2 ^ 255 - 19)%Z)
    with ((-1) mod (2^255 - 19)) %Z.
    rewrite -lock //=.
    apply legendre_compute.
  + rename n0 into H.
    apply /negP => Hx.
    apply H.
    move: Hx.
    move /eqP => Hx.
    apply (f_equal (fun x => Zmodp.repr x)) in Hx.
    exists (Zmodp.repr x).
    move: Hx.
    rewrite expr2.
    rewrite Z.pow_2_r.
    rewrite modZp => <- //.
Qed.

Definition twist25519_ladder n x :=
  @opt_montgomery twist25519_finECUFieldType twist25519_mcuType n 255 x.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Theorem twist25519_ladder_ok (n : nat) x :
    (n < 2^255)%nat -> x != 0 ->
    forall (p : mc twist25519_mcuType), p#x0 = x -> twist25519_ladder n x = (p *+ n)#x0.
Proof.
move => Hn Hx p Hp.
rewrite /twist25519_ladder.
apply opt_montgomery_ok => //=.
apply twist25519_residute.
Qed.
