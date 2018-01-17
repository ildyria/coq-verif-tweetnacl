Set Warnings "-notation-overridden".
Require Export Coq.ZArith.ZArith.
Require Import Tweetnacl.Libs.Decidable.
(* Require Import ssreflect. *)
Require Import Recdef.
Open Scope Z_scope.

Section fun_rec.

Context {T:Type} (n:Z). (* (Hn : 0 <= n). *)

Definition dec_proof_fun (n a  : Z) : nat := Z.to_nat (a - n).

Function sub_fn_rev_1 (f:Z -> T -> T) (a:Z) (t: T) {measure (dec_proof_fun n) a} : T :=
  if (a <=? n)
    then t
    else
      let prev := sub_fn_rev_1 f (a - 1) t in 
        f (a - 1) prev.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.


Function sub_fn_rev_2 (f:Z -> T -> T -> T) (a:Z) (m t: T) {measure (dec_proof_fun n) a} : T :=
  if (a <=? n)
    then m
    else
      let prev := sub_fn_rev_2 f (a - 1) m t in 
        f (a - 1) prev t.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

End fun_rec.


Section fun_rec_denote_1.

Context {T:Type}.
Context {U:Type}.
Context (t_inst : @Decidable T U).
Context (f_inst : @Decidable (Z -> T -> T) (Z -> U -> U)).
Context (f_t : forall env (z:Z) (f: Z -> T -> T) (t:T), denote env (f z t) = (denote env f) z (denote env t)).

Inductive fun_rec_dec_1 :=
  | Fun_n : Z -> Z -> (Z -> T -> T) -> T -> fun_rec_dec_1.

Definition fun_rec_denote env (f:fun_rec_dec_1) : (U) := match f with
  | Fun_n n z f' t => sub_fn_rev_1 n (denote env f') z (denote env t)
  end.

Definition fun_rec_denote_full env (f:fun_rec_dec_1) : (U) := match f with
  | Fun_n n z f' t => denote env (sub_fn_rev_1 n f' z t)
  end.

Lemma fun_rec_denote_full_impl : forall env l, fun_rec_denote env l = fun_rec_denote_full env l.
Proof.
intros env.
destruct l as [n z f t].
simpl.
rewrite sub_fn_rev_1_equation ; symmetry ; rewrite sub_fn_rev_1_equation ; symmetry.
destruct (z <=? n) eqn:?.
reflexivity.
rewrite Z.leb_gt in Heqb.
pattern z.
match goal with
  | [ |- ?F _ ] => apply (Zlt_lower_bound_ind F n)
end.
2: omega.
intros.
rewrite sub_fn_rev_1_equation ; symmetry ; rewrite sub_fn_rev_1_equation ; symmetry.
destruct (x - 1 <=? n) eqn:?.
rewrite f_t ; reflexivity.
rewrite Z.leb_gt in Heqb0.
rewrite f_t.
f_equal.
apply H.
omega.
Qed.

Definition fun_rec_decide (l l' : fun_rec_dec_1) : bool := match l, l' with
  | Fun_n n z f t, Fun_n n' z' f' t' => decide (sub_fn_rev_1 n f z t) (sub_fn_rev_1 n' f' z' t')
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

End fun_rec_denote_1.

Close Scope Z.