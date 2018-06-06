Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import step_gen.

Section Abstract_Rec.

Context {T : Type}.
Context {O : Ops T}.

Fixpoint abstract_rec (m : nat) (z a b c d e f x : T) : (T * T * T * T * T * T) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat n) z in
      abstract_rec n z 
        (fa r a b c d e f x)
        (fb r a b c d e f x)
        (fc r a b c d e f x)
        (fd r a b c d e f x)
        (fe r a b c d e f x)
        (ff r a b c d e f x)
        x
    end.

Arguments rec_fn [T] _ _ _.

(* Definition abstract_rec_fn (z x:T) (n:nat) (a b c d e f : T) := rec_fn (step_gen z x) n (a,b,c,d,e,f). *)

Lemma abstract_rec_equiv_rec_fn: forall n z a b c d e f x,
  abstract_rec n z a b c d e f x = rec_fn (step_gen z x) n (a,b,c,d,e,f).
Proof.
  induction n => z x a b c d e f.
  reflexivity.
  simpl.
  apply IHn.
Qed.

End Abstract_Rec.