Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import step_gen.

Section Abstract_Rec.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Fixpoint abstract_rec (m : nat) (z:T') (a b c d e f x : T) : (T * T * T * T * T * T) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := Getbit (Z.of_nat n) z in
      abstract_rec n z 
        (Gen.fa r a b c d e f x)
        (Gen.fb r a b c d e f x)
        (Gen.fc r a b c d e f x)
        (Gen.fd r a b c d e f x)
        (Gen.fe r a b c d e f x)
        (Gen.ff r a b c d e f x)
        x
    end.

Arguments rec_fn [T] _ _ _.

Lemma abstract_rec_equiv_rec_fn: forall n z a b c d e f x,
  abstract_rec n z a b c d e f x = rec_fn (step_gen z x) n (a,b,c,d,e,f).
Proof.
  induction n => z x a b c d e f.
  reflexivity.
  simpl.
  apply IHn.
Qed.

End Abstract_Rec.