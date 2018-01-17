Set Warnings "-notation-overridden".
Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Import Tweetnacl.Libs.Decidable.
Require Import Tweetnacl.Libs.Expr_Decidable.
Require Import Tweetnacl.Libs.Term_Decidable.
Require Import ssreflect.

Open Scope Z_scope.

Section list_denote.

Context {T} {U} (inst : @Decidable T U).

Fixpoint list_denote env (l: list T) : list U :=
  match l with
    | nil => nil
    | h :: q => (denote env h) :: list_denote env q
  end.

(*****************************************************************************************
 *   DECIDE EQUALITY
 *)

Fixpoint list_decide (l l' : list T) : bool := match l, l' with
  | nil, nil => true
  | a :: qa , b :: qb => andb (decide a b) (list_decide qa qb)
  | _, _ => false
  end.

Lemma list_decide_impl:
  forall env a b,
    list_decide a b = true ->
    list_denote env a = list_denote env b.
Proof.
  induction a as [|a qa IHa] => b H.
  destruct b.
  reflexivity.
  simpl in H ; congruence.
  destruct b.
  simpl in H ; congruence.
  simpl in *.
  apply Bool.andb_true_iff in H.
  destruct H.
  f_equal.
  by apply decide_impl.
  by apply IHa.
Qed.

End list_denote.

(********************************************************************************)

Local Definition ta := Var 1%positive.
Local Definition tb := Var 2%positive.
Local Definition tc := Var 3%positive.
Local Definition td := Var 4%positive.
Local Definition te := Var 5%positive.
Local Definition tf := Var 6%positive.
Local Definition tg := Var 7%positive.

Local Definition expr1 := A (M ta tb) (A (R tc) (R tb)).
Local Definition expr2 := A (A (R tc) (R tb)) (M ta tb).

Inductive formula :=
  | Eq : expr -> expr -> formula
  | LEq : list expr -> list expr -> formula.

Definition formula_denote env (t : formula) : Prop :=
  match t with
  | Eq x y     => denote env x = denote env y
  | LEq x y    => list_denote expr_dec env x = list_denote expr_dec env y
  end.

Definition formula_decide (f : formula) : bool := match f with
  | Eq x y => decide x y
  | LEq x y => list_decide expr_dec x y
  end.

Lemma formula_decide_impl : forall env f, formula_decide f = true -> formula_denote env f.
Proof. move=> env [? ?| ? ?]. by apply decide_impl. by apply list_decide_impl. Qed.

Local Example test2: formula_decide (Eq expr1 expr2) = true.
Proof.
by compute.
Qed.

Local Example test3: formula_decide (LEq (expr1::nil) (expr2::nil)) = true.
Proof.
by compute.
Qed.

Close Scope Z.