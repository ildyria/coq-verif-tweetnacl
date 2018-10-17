Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.

Section last_in.

Open Scope Z.

Context (U:Type).
Context (T:Type).
Context (T':Type).

Fixpoint fun_rec (f_last: U -> T) (f_in: nat -> T' -> U -> U) (m : nat) (z : T') (x : U) : T :=
  match m with
  | 0%nat => f_last x
  | S n => fun_rec f_last f_in n z (f_in n z x) 
    end.

Fixpoint fun_rec_0 (f_in: nat -> T' -> U -> U) (m : nat) (z : T') (x : U) : U :=
  match m with
  | 0%nat => x
  | S n => fun_rec_0 f_in n z (f_in n z x)
   end.

Lemma fun_rec_extract_last: forall f_in f_last n z x,
  f_last (fun_rec_0 f_in n z x) = fun_rec f_last f_in  n z x.
Proof.
intros f_in f_last n.
induction n as [|n IHn]; intros z x.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.

Close Scope Z.

End last_in.