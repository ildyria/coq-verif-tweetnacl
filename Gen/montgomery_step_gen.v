Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import step_gen.

Section Montgomery_Step_Gen.

Context {T : Type}.
Context {O : Ops T}.

Definition montgomery_step_gen (m:nat) (z a b c d e f x : T) : (T * T * T * T * T * T)  :=
      let r := getbit (Z.of_nat m) z in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      let e := A a c in
      let a := Zub a c in
      let c := A b d in
      let b := Zub b d in
      let d := Sq e in
      let f := Sq a in
      let a := M c a in
      let c := M b e in
      let e := A a c in
      let a := Zub a c in
      let b := Sq a in
      let c := Zub d f in
      let a := M c _121665 in
      let a := A a d in
      let c := M c a in
      let a := M d f in
      let d := M b x in
      let b := Sq e in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      (a,b,c,d,e,f).

Lemma montgomery_step_gen_eq: forall n z a b c d e f x,
  step_gen z x n (a, b, c, d, e, f) = montgomery_step_gen n z a b c d e f x.
Proof. intros. reflexivity. Qed.

End Montgomery_Step_Gen.