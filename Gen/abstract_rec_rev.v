Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import step_gen.

Section Abstract_Rec_Rev.

Context {T : Type}.
Context {T' : Type}.
Context {O : Ops T T'}.

Fixpoint abstract_rec_rev m p (z:T') (a b c d e f x : T) : (T * T * T * T * T * T)
  :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      match (abstract_rec_rev n p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := Getbit (Z.of_nat (p - n)) z in
        (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end
  end.

Arguments rec_fn_rev_acc [T] _ _ _.
Arguments rec_fn_rev [T] _ _.

Local Lemma abstract_rec_rev_equiv_rev_fn_p : forall n p z a b c d e f x,
  abstract_rec_rev n (p - 1) z a b c d e f x = rec_fn_rev_acc (step_gen z x) n p (a,b,c,d,e,f).
Proof.
  induction n => p z x a b c d e f.
  reflexivity.
  simpl.
  replace (p - n - 1) with (p - 1 - n).
  2: omega.
  remember((rec_fn_rev_acc (step_gen z f) n p (x, a, b, c, d, e))) as k.
  destruct k as (((((a0,b0),c0),d0),e0),f0).
  remember (abstract_rec_rev n (p - 1) z x a b c d e f ) as k'.
  destruct k' as (((((a1,b1),c1),d1),e1),f1).
  assert(IH := IHn p z x a b c d e f).
  go.
Qed.

Theorem abstract_rec_rev_equiv_rec_fn_S_n : forall n z a b c d e f x,
  abstract_rec_rev (S n) n z a b c d e f x = rec_fn_rev (step_gen z x) (S n) (a,b,c,d,e,f).
Proof. intros. rewrite /rec_fn_rev -abstract_rec_rev_equiv_rev_fn_p.
replace (S n - 1) with n ; go.
Qed.

End Abstract_Rec_Rev.