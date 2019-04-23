Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import curve25519_prime_cert.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
From Tweetnacl.High Require Import Zmodp.
Import BinInt.

Require Import Ring.
Open Scope ring_scope.
Import GRing.Theory.

Local Lemma a_2_4 : (Zmodp.pi 486662) ^+ 2 - 4%:R = Zmodp.pi 236839902240.
Proof.
rewrite expr2 Zmodp_mulE /= Zmodp_oppE /= /Zmodp.p -lock /= Zmodp_addE //=.
Qed.

Lemma a_not_square (x : Zmodp.type) : x ^+ 2 != (Zmodp.pi 486662) ^+ 2 - 4%:R.
Proof.
rewrite a_2_4.
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

Close Scope ring_scope.
