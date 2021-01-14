(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite set as unordered lists without duplicates
removed. This implementation forms a monad. *)
From stdpp Require Export collections list.
Set Default Proof Using "Type".

Record listset A := Listset { listset_car: list A }.
Arguments listset_car {_} _ : assert.
Arguments Listset {_} _ : assert.

Section listset.
Context {A : Type}.

Global Instance listset_elem_of: ElemOf A (listset A) := λ x l, x ∈ listset_car l.
Global Instance listset_empty: Empty (listset A) := Listset [].
Global Instance listset_singleton: Singleton A (listset A) := λ x, Listset [x].
Global Instance listset_union: Union (listset A) := λ l k,
  let (l') := l in let (k') := k in Listset (l' ++ k').
Global Opaque listset_singleton listset_empty.

Global Instance listset_simple_collection : SimpleCollection A (listset A).
Proof.
  split.
  - by apply not_elem_of_nil.
  - by apply elem_of_list_singleton.
  - intros [?] [?]. apply elem_of_app.
Qed.
Lemma listset_empty_alt X : X ≡ ∅ ↔ listset_car X = [].
Proof.
  destruct X as [l]; split; [|by intros; simplify_eq/=].
  rewrite elem_of_equiv_empty; intros Hl.
  destruct l as [|x l]; [done|]. feed inversion (Hl x). left.
Qed. 
Global Instance listset_empty_dec (X : listset A) : Decision (X ≡ ∅).
Proof.
 refine (cast_if (decide (listset_car X = [])));
  abstract (by rewrite listset_empty_alt).
Defined.

Context `{!EqDecision A}.

Global Instance listset_intersection: Intersection (listset A) := λ l k,
  let (l') := l in let (k') := k in Listset (list_intersection l' k').
Global Instance listset_difference: Difference (listset A) := λ l k,
  let (l') := l in let (k') := k in Listset (list_difference l' k').

Instance listset_collection: Collection A (listset A).
Proof.
  split.
  - apply _.
  - intros [?] [?]. apply elem_of_list_intersection.
  - intros [?] [?]. apply elem_of_list_difference.
Qed.
Global Instance listset_elements: Elements A (listset A) :=
  remove_dups ∘ listset_car.
Global Instance listset_fin_collection : FinCollection A (listset A).
Proof.
  split.
  - apply _.
  - intros. apply elem_of_remove_dups.
  - intros. apply NoDup_remove_dups.
Qed.
End listset.

Instance listset_ret: MRet listset := λ A x, {[ x ]}.
Instance listset_fmap: FMap listset := λ A B f l,
  let (l') := l in Listset (f <$> l').
Instance listset_bind: MBind listset := λ A B f l,
  let (l') := l in Listset (mbind (listset_car ∘ f) l').
Instance listset_join: MJoin listset := λ A, mbind id.

Instance listset_collection_monad : CollectionMonad listset.
Proof.
  split.
  - intros. apply _.
  - intros ??? [?] ?. apply elem_of_list_bind.
  - intros. apply elem_of_list_ret.
  - intros ??? [?]. apply elem_of_list_fmap.
  - intros ? [?] ?. unfold mjoin, listset_join, elem_of, listset_elem_of.
    simpl. by rewrite elem_of_list_bind.
Qed.
