Set Warnings "-funind-cannot-define-graph".
Set Warnings "-funind".

Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import step_gen.

Section Abstract_Fn_Rev.

Open Scope Z.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Function abstract_fn_rev (m p:Z) (z:T') (a b c d e f x:T) {measure Z.to_nat m} : (T * T * T * T * T * T) :=
  if (m <=? 0)
    then (a,b,c,d,e,f)
    else 
    match (abstract_fn_rev (m - 1) p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := Getbit (p - (m - 1)) z in
        (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma abstract_fn_rev_0 : forall p z a b c d e f x,
  abstract_fn_rev 0 p z a b c d e f x = (a,b,c,d,e,f).
Proof. move=> p z a b c d e f x ; reflexivity. Qed.

Lemma abstract_fn_rev_n : forall n p z a b c d e f x,
  0 < n ->
  abstract_fn_rev n p z a b c d e f x =
   match (abstract_fn_rev (n - 1) p z a b c d e f x) with
        | (a,b,c,d,e,f) =>
        let r := Getbit (p - (n - 1)) z in
        (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end.
Proof. move=> n p z a b c d e f x Hn.
rewrite abstract_fn_rev_equation.
assert((n <=? 0) = false).
by apply Z.leb_gt. flatten.
Qed.

Close Scope Z.

End Abstract_Fn_Rev.
