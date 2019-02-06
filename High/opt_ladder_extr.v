Set Warnings "-notation-overridden,-parsing".

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Export opt_ladder.

From Tweetnacl.Gen Require Import Get_abcdef.

Import GRing.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Section OptimizedLadder.
  Variable K : finECUFieldType.
  Variable M : mcuType K.

  Fixpoint opt_montgomery_rec_extr (n m : nat) (x a b c d : K) : (K * K * K * K * K * K) :=
    if m is m.+1 then
      let (a, b) := cswap (bitn n m) a b in
      let (c, d) := cswap (bitn n m) c d in
      let e := a + c in
      let a := a - c in
      let c := b + d in
      let b := b - d in
      let d := e^+2 in
      let f := a^+2 in
      let a := c * a in
      let c := b * e in
      let e := a + c in
      let a := a - c in
      let b := a^+2 in
      let c := d - f in
      let a := c * ((M#a - 2%:R) / 4%:R) in
      let a := a + d in
      let c := c * a in
      let a := d * f in
      let d := b * x in
      let b := e^+2 in
      let (a, b) := cswap (bitn n m) a b in
      let (c, d) := cswap (bitn n m) c d in
      opt_montgomery_rec_extr n m x a b c d
    else
      (a,0,c,0,0,0).


Lemma opt_montgomery_rec_equiv:
  forall m n x a b c d,
  opt_montgomery_rec M n m x a b c d = get_a (opt_montgomery_rec_extr n m x a b c d) / get_c (opt_montgomery_rec_extr n m x a b c d).
Proof.
elim => [|m IHm] n x a b c d //=.
by do! case: (cswap _ _ _) => *.
(* or... *)
(* by repeat match goal with
  | [|- context[(cswap (bitn ?N ?M) ?A ?B)] ] => let H := fresh "H" in destruct (cswap (bitn N M) A B) eqn:H; rewrite ?H
end. *)
Qed.

End OptimizedLadder.
