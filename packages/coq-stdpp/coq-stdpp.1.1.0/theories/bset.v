(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements bsets as functions into Prop. *)
From stdpp Require Export prelude.
Set Default Proof Using "Type".

Record bset (A : Type) : Type := mkBSet { bset_car : A → bool }.
Arguments mkBSet {_} _ : assert.
Arguments bset_car {_} _ _ : assert.

Instance bset_top {A} : Top (bset A) := mkBSet (λ _, true).
Instance bset_empty {A} : Empty (bset A) := mkBSet (λ _, false).
Instance bset_singleton `{EqDecision A} : Singleton A (bset A) := λ x,
  mkBSet (λ y, bool_decide (y = x)).
Instance bset_elem_of {A} : ElemOf A (bset A) := λ x X, bset_car X x.
Instance bset_union {A} : Union (bset A) := λ X1 X2,
  mkBSet (λ x, bset_car X1 x || bset_car X2 x).
Instance bset_intersection {A} : Intersection (bset A) := λ X1 X2,
  mkBSet (λ x, bset_car X1 x && bset_car X2 x).
Instance bset_difference {A} : Difference (bset A) := λ X1 X2,
  mkBSet (λ x, bset_car X1 x && negb (bset_car X2 x)).
Instance bset_collection `{EqDecision A} : Collection A (bset A).
Proof.
  split; [split| |].
  - by intros x ?.
  - by intros x y; rewrite <-(bool_decide_spec (x = y)).
  - split. apply orb_prop_elim. apply orb_prop_intro.
  - split. apply andb_prop_elim. apply andb_prop_intro.
  - intros X Y x; unfold elem_of, bset_elem_of; simpl. 
    destruct (bset_car X x), (bset_car Y x); simpl; tauto.
Qed.
Instance bset_elem_of_dec {A} : RelDecision (@elem_of _ (bset A) _).
Proof. refine (λ x X, cast_if (decide (bset_car X x))); done. Defined.

Typeclasses Opaque bset_elem_of.
Global Opaque bset_empty bset_singleton bset_union
  bset_intersection bset_difference.
