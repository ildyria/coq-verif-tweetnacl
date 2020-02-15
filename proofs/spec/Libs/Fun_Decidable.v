Set Warnings "-notation-overridden".
Require Export Coq.ZArith.ZArith.
Require Import Tweetnacl.Libs.Decidable.
Require Import Recdef.
Open Scope Z_scope.

Section fun_rec.

Context {T:Type} (n:Z).

Definition dec_proof_fun (n a  : Z) : nat := Z.to_nat (a - n).


Function sub_fn_rev (f:Z -> T -> T -> T) (a:Z) (m t: T) {measure (dec_proof_fun n) a} : T :=
  if (a <=? n)
    then m
    else
      let prev := sub_fn_rev f (a - 1) m t in 
        f (a - 1) prev t.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Lemma sub_fn_rev_1 : forall (f: Z -> T -> T -> T) (m t:T),
  sub_fn_rev f n m t = m.
Proof. intros. rewrite sub_fn_rev_equation ; rewrite Z.leb_refl ; reflexivity. Qed.

Lemma sub_fn_rev_n : forall (a:Z) (f: Z -> T -> T -> T) (m t:T),
  n < a ->
  sub_fn_rev f a m t = f (a - 1) (sub_fn_rev f (a - 1) m t) t.
Proof. intros. rewrite sub_fn_rev_equation. replace (a <=? n) with false. reflexivity.
symmetry ; apply Z.leb_gt ; assumption. Qed.

Function sub_fn_rev_s (f:Z -> T -> T) (a:Z) (t: T) {measure (dec_proof_fun n) a} : T :=
  if (a <=? n)
    then t
    else
      let prev := sub_fn_rev_s f (a - 1) t in 
        f (a - 1) prev.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Lemma sub_fn_rev_s_1 : forall (f: Z -> T -> T) (t:T),
  sub_fn_rev_s f n t = t.
Proof. intros. rewrite sub_fn_rev_s_equation ; rewrite Z.leb_refl ; reflexivity. Qed.

Lemma sub_fn_rev_s_n : forall (a:Z) (f: Z -> T -> T) (t:T),
  n < a ->
  sub_fn_rev_s f a t = f (a - 1) (sub_fn_rev_s f (a - 1) t).
Proof. intros. rewrite sub_fn_rev_s_equation. replace (a <=? n) with false. reflexivity.
symmetry ; apply Z.leb_gt ; assumption. Qed.

End fun_rec.


Section fun_rec_denote_s.

Context {T:Type}.
Context {U:Type}.
Context (t_inst : @Decidable T U).
Context (f_inst : @Decidable (Z -> T -> T) (Z -> U -> U)).
Context (f_t : forall env (z:Z) (f: Z -> T -> T) (t:T), denote env (f z t) = (denote env f) z (denote env t)).

Inductive fun_rec_dec_s :=
  | Fun_n : Z -> Z -> (Z -> T -> T) -> T -> fun_rec_dec_s.

Definition fun_rec_denote env (f:fun_rec_dec_s) : (U) := match f with
  | Fun_n n z f' t => sub_fn_rev_s n (denote env f') z (denote env t)
  end.

Definition fun_rec_denote_full env (f:fun_rec_dec_s) : (U) := match f with
  | Fun_n n z f' t => denote env (sub_fn_rev_s n f' z t)
  end.

Lemma fun_rec_denote_full_impl : forall env l, fun_rec_denote env l = fun_rec_denote_full env l.
Proof.
intros env.
destruct l as [n z f t].
simpl.
rewrite sub_fn_rev_s_equation ; symmetry ; rewrite sub_fn_rev_s_equation ; symmetry.
destruct (z <=? n) eqn:?.
reflexivity.
rewrite Z.leb_gt in Heqb.
pattern z.
match goal with
  | [ |- ?F _ ] => apply (Zlt_lower_bound_ind F n)
end.
2: omega.
intros.
rewrite sub_fn_rev_s_equation ; symmetry ; rewrite sub_fn_rev_s_equation ; symmetry.
destruct (x - 1 <=? n) eqn:?.
rewrite f_t ; reflexivity.
rewrite Z.leb_gt in Heqb0.
rewrite f_t.
f_equal.
apply H.
omega.
Qed.

Definition fun_rec_decide (l l' : fun_rec_dec_s) : bool := match l, l' with
  | Fun_n n z f t, Fun_n n' z' f' t' => decide (sub_fn_rev_s n f z t) (sub_fn_rev_s n' f' z' t')
  end.

Lemma fun_rec_decide_impl : forall env l l',
  fun_rec_decide l l' = true -> fun_rec_denote env l = fun_rec_denote env l'.
Proof.
  intros env.
  destruct l as [n z f t].
  destruct l' as [n' z' f' t'].
  intros H.
  simpl in H.
  apply (decide_impl env) in H.
  rewrite ?fun_rec_denote_full_impl.
  simpl.
  assumption.
Qed.

End fun_rec_denote_s.

Close Scope Z.