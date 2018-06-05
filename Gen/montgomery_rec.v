Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import montgomery_step_gen.

Section Montgomery_Rec.

Context {T : Type}.
Context {O : Ops T}.

Open Scope Z.

Fixpoint montgomery_rec (m : nat) (z a b c d e f x : T) : (T * T * T * T * T * T) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat n) z in
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
      montgomery_rec n z a b c d e f x
    end.

Lemma opt_montgomery_rec_step_gen : forall n z a b c d e f x,
  montgomery_rec (S n) z a b c d e f x = 
  montgomery_rec n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof. reflexivity. Qed.

Lemma opt_montgomery_rec_step_gen_ext : forall n z a b c d e f e' f' x,
  montgomery_rec (S n) z a b c d e' f' x = 
  montgomery_rec n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof. reflexivity. Qed.

Close Scope Z.

End Montgomery_Rec.