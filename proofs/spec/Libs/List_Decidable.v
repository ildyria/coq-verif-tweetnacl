Set Warnings "-notation-overridden".
Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Import Tweetnacl.Libs.Decidable.
Require Import Tweetnacl.Libs.Expr_Decidable.
Require Import Tweetnacl.Libs.Term_Decidable.
Require Import Tweetnacl.Libs.Formula_Decidable.
Require Import Tweetnacl.Libs.Lists_extended.
Require Import ssreflect.

Open Scope Z_scope.

Section list_denote.

Context {T} {U} {inst : @Decidable T U}.

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

Lemma list_denote_nth :
  forall i env (l: list T) (d:T), denote env (nth i l d) = nth i (list_denote env l) (denote env d).
Proof.
intros i env l. revert i. induction l as [|h l IHl] ; intros [|i] ; try reflexivity.
simpl. apply IHl.
Qed.

Lemma list_denote_firstn :
  forall i env (l: list T), list_denote env (firstn i l) = firstn i (list_denote env l).
Proof.
intros i env l. revert i. induction l as [|h l IHl] ; intros [|i] ; try reflexivity.
simpl. rewrite IHl ; reflexivity.
Qed.

Lemma list_denote_skipn :
  forall i env (l: list T), list_denote env (skipn i l) = skipn i (list_denote env l).
Proof.
intros i env l. revert i. induction l as [|h l IHl] ; intros [|i] ; try reflexivity.
simpl. rewrite IHl ; reflexivity.
Qed.

Lemma list_denote_map :
  forall env (l: list T), map (denote env) l = (list_denote env l).
Proof.
induction l as [|h l IHl] ; try reflexivity.
simpl. rewrite IHl ; reflexivity.
Qed.

Lemma list_denote_length:
  forall env (l:list T), length (list_denote env l) = length l.
Proof.
intros. rewrite -list_denote_map map_length ; reflexivity.
Qed.

Lemma list_denote_Zlength:
  forall env (l:list T), Zlength (list_denote env l) = Zlength l.
Proof.
intros. rewrite -list_denote_map Zlength_map ; reflexivity.
Qed.

Lemma list_denote_upd_nth :
  forall i env (l: list T) (v:T), list_denote env (upd_nth i l v) = upd_nth i (list_denote env l) (denote env v).
Proof.
intros i env m. revert i. induction m as [|h m IHm] ; intros [|i] v ; try reflexivity.
simpl. f_equal. apply IHm.
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

Local Instance term_dec : Decidable := Build_Decidable _ _ term_decide term_denote term_decide_impl.
Local Instance list_term_dec : Decidable := Build_Decidable (list term) (list Z)
  list_decide list_denote list_decide_impl.

Local Instance expr_dec : Decidable := Build_Decidable _ _ expr_decide expr_denote expr_decide_impl.
Local Instance list_expr_dec : Decidable := Build_Decidable (list expr) (list Z)
  list_decide list_denote list_decide_impl.

Local Example test2: formula_decide (Eq expr1 expr2) = true.
Proof.
by compute.
Qed.

Local Example test3: formula_decide (Eq (expr1::nil) (expr2::nil)) = true.
Proof.
by compute.
Qed.

Close Scope Z.