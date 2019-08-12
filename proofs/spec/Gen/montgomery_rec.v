Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.

Section Montgomery_Rec.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Open Scope Z.

Local Notation "X + Y" := (A X Y) (only parsing).
Local Notation "X - Y" := (Zub X Y) (only parsing).
Local Notation "X * Y" := (M X Y) (only parsing).
Local Notation "X ^2" := (Sq X) (at level 40, only parsing, left associativity).

Fixpoint montgomery_rec (m : nat) (z : T') (a b c d e f x : T) : (T * T * T * T * T * T) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := Getbit (Z.of_nat n) z in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      let e := a + c in
      let a := a - c in
      let c := b + d in
      let b := b - d in
      let d := e ^2 in
      let f := a ^2 in
      let a := c * a in
      let c := b * e in
      let e := a + c in
      let a := a - c in
      let b := a ^2 in
      let c := d - f in
      let a := c * C_121665 in
      let a := a + d in
      let c := c * a in
      let a := d * f in
      let d := b * x in
      let b := e ^2 in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      montgomery_rec n z a b c d e f x
    end.

Close Scope Z.

End Montgomery_Rec.