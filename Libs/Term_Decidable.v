Set Warnings "-notation-overridden".

Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Import Coq.Sorting.Sorting Orders.
Require Import ssreflect.
Require Import Tweetnacl.Libs.Decidable.

Open Scope Z_scope.

Inductive term :=
  | Var   : positive -> term
  | Val   : Z -> term
  .

Definition term_decide (x y : term) : bool := match x , y with
  | Var x , Var y => Pos.eqb x y
  | Val x,  Val y => Z.eqb x y
  | _, _ => false
  end.

Lemma term_eqb_refl : forall x y, term_decide x y = true <-> x = y.
Proof.
move => x y ; rewrite /term_decide ; split => H ; simpl.
destruct x,y; move: H.
rewrite Pos.eqb_eq => -> //.
discriminate.
discriminate.
rewrite Z.eqb_eq => -> //.
subst ; destruct y.
rewrite Pos.eqb_eq //.
rewrite Z.eqb_eq //.
Qed.

Definition term_denote (env:environment) (x : term) : Z :=
  match x with
  | Var n => vars env n
  | Val n => n
  end.

Lemma term_decide_com : forall x y, term_decide x y = term_decide y x.
Proof.
move => [] a [] b //=.
rewrite ?Pos2Z.inj_eqb.
apply Z.eqb_sym.
apply Z.eqb_sym.
Qed.

Definition term_leb (x y : term) : bool := match x , y with
  | Var x , Var y => Pos.leb x y
  | Val x , Val y => Z.leb x y
  | Var x,  Val y => false
  | Val x,  Var y => true
  end.

Definition term_ltb (x y : term) : bool := match x , y with
  | Var x , Var y => Pos.ltb x y
  | Val x , Val y => Z.ltb x y
  | Var x,  Val y => false
  | Val x,  Var y => true
  end.

Lemma term_decide_impl : forall (env : environment) (a b : term),
term_decide a b = true -> term_denote env a = term_denote env b.
Proof. intros. apply term_eqb_refl in H. subst a. reflexivity. Qed.

Instance term_dec : Decidable := 
{
  decide := term_decide;
  denote := term_denote;
  decide_impl := term_decide_impl
}.

Close Scope Z.