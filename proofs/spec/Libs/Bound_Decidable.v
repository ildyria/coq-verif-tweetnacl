(* Set Warnings "-notation-overridden".

Require Export Coq.ZArith.ZArith.
(* Require Export Coq.Lists.List. *)
(* Require Import Coq.Sorting.Sorting Orders. *)
(* Require Import ssreflect. *)
Require Import Tweetnacl.Libs.Decidable.
(* Require Import Tweetnacl.Libs.Term_Decidable. *)

Open Scope Z_scope.

(* Local Instance term_dec : Decidable := 
{
  decide := term_decide;
  denote := term_denote;
  decide_impl := term_decide_impl
}.

*)
Section Bound.

(* Context {A:Type}.
 *)
  Inductive bound :=
    | LE_inf : Z -> Z -> bound
    | LT_inf : Z -> Z -> bound
    | LE_sup : Z -> Z -> bound
    | LT_sup : Z -> Z -> bound.

  Fixpoint expr_denote (env:environment) (m : bound) : Prop :=
    match m with
    | LE_inf z a => z <= a
    | LT_inf z a => z < a
    | LE_sup z a => a <= z
    | LT_sup z a => a < z
   end.

  Inductive bound_formula :=
    | Bound_sgl : bound -> bound_formula
    | Bound_And : bound_formula -> bound_formula -> bound_formula
    | Bound_Impl : bound_formula -> bound_formula.

End Bound.


Close Scope Z. *)