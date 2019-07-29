Require Import Omega.
Require Import ssreflect.
Section ScalarRec.

Variable T:Type.
Variable g : nat -> T -> T.

Fixpoint rec_fn (n:nat) (s:T) := match n with
  | 0 => s
  | S n => (rec_fn n (g n s))
  end.

Fixpoint rec_fn_rev_acc (n:nat) (m:nat) (s:T) := match n with
  | 0 => s
  | S n => g (m - n - 1) (rec_fn_rev_acc n m s)
  end.

Definition rec_fn_rev (n:nat) (s:T) :=
  rec_fn_rev_acc n n s.

Lemma rec_fn_rev_acc_S : forall m n s,
  rec_fn_rev_acc (S n) (S m) s = rec_fn_rev_acc n m (g m s).
Proof.
  induction n => s. simpl.
  by rewrite Nat.sub_0_r .
  change (rec_fn_rev_acc (S (S n)) (S m) s) with (g (S m - S n - 1) (rec_fn_rev_acc (S n) (S m) s)).
  rewrite IHn.
  simpl.
  reflexivity.
Qed.

Theorem Tail_Head_equiv : forall n s, rec_fn n s = rec_fn_rev n s.
Proof.
  induction n => s //.
  rewrite /rec_fn_rev rec_fn_rev_acc_S.
  simpl.
  by rewrite IHn.
Qed.

End ScalarRec.
