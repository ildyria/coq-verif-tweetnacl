(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files extends the implementation of finite over [positive] to finite
maps whose keys range over Coq's data type of binary naturals [N]. *)
From stdpp Require Import pmap mapset.
From stdpp Require Export prelude fin_maps.
Set Default Proof Using "Type".

Local Open Scope N_scope.

Record Nmap (A : Type) : Type := NMap { Nmap_0 : option A; Nmap_pos : Pmap A }.
Arguments Nmap_0 {_} _ : assert.
Arguments Nmap_pos {_} _ : assert.
Arguments NMap {_} _ _ : assert.

Instance Nmap_eq_dec `{EqDecision A} : EqDecision (Nmap A).
Proof.
 refine (λ t1 t2,
  match t1, t2 with
  | NMap x t1, NMap y t2 => cast_if_and (decide (x = y)) (decide (t1 = t2))
  end); abstract congruence.
Defined.
Instance Nempty {A} : Empty (Nmap A) := NMap None ∅.
Global Opaque Nempty.
Instance Nlookup {A} : Lookup N A (Nmap A) := λ i t,
  match i with
  | N0 => Nmap_0 t
  | Npos p => Nmap_pos t !! p
  end.
Instance Npartial_alter {A} : PartialAlter N A (Nmap A) := λ f i t,
  match i, t with
  | N0, NMap o t => NMap (f o) t
  | Npos p, NMap o t => NMap o (partial_alter f p t)
  end.
Instance Nto_list {A} : FinMapToList N A (Nmap A) := λ t,
  match t with
  | NMap o t =>
     default [] o (λ x, [(0,x)]) ++ (prod_map Npos id <$> map_to_list t)
  end.
Instance Nomap: OMap Nmap := λ A B f t,
  match t with NMap o t => NMap (o ≫= f) (omap f t) end.
Instance Nmerge: Merge Nmap := λ A B C f t1 t2,
  match t1, t2 with
  | NMap o1 t1, NMap o2 t2 => NMap (f o1 o2) (merge f t1 t2)
  end.
Instance Nfmap: FMap Nmap := λ A B f t,
  match t with NMap o t => NMap (f <$> o) (f <$> t) end.

Instance: FinMap N Nmap.
Proof.
  split.
  - intros ? [??] [??] H. f_equal; [apply (H 0)|].
    apply map_eq. intros i. apply (H (Npos i)).
  - by intros ? [|?].
  - intros ? f [? t] [|i]; simpl; [done |]. apply lookup_partial_alter.
  - intros ? f [? t] [|i] [|j]; simpl; try intuition congruence.
    intros. apply lookup_partial_alter_ne. congruence.
  - intros ??? [??] []; simpl. done. apply lookup_fmap.
  - intros ? [[x|] t]; unfold map_to_list; simpl.
    + constructor.
      * rewrite elem_of_list_fmap. by intros [[??] [??]].
      * by apply (NoDup_fmap _), NoDup_map_to_list.
    + apply (NoDup_fmap _), NoDup_map_to_list.
  - intros ? t i x. unfold map_to_list. split.
    + destruct t as [[y|] t]; simpl.
      * rewrite elem_of_cons, elem_of_list_fmap.
        intros [? | [[??] [??]]]; simplify_eq/=; [done |].
        by apply elem_of_map_to_list.
      * rewrite elem_of_list_fmap; intros [[??] [??]]; simplify_eq/=.
        by apply elem_of_map_to_list.
    + destruct t as [[y|] t]; simpl.
      * rewrite elem_of_cons, elem_of_list_fmap.
        destruct i as [|i]; simpl; [intuition congruence |].
        intros. right. exists (i, x). by rewrite elem_of_map_to_list.
      * rewrite elem_of_list_fmap.
        destruct i as [|i]; simpl; [done |].
        intros. exists (i, x). by rewrite elem_of_map_to_list.
  - intros ?? f [??] [|?]; simpl; [done|]; apply (lookup_omap f).
  - intros ??? f ? [??] [??] [|?]; simpl; [done|]; apply (lookup_merge f).
Qed.

(** * Finite sets *)
(** We construct sets of [N]s satisfying extensional equality. *)
Notation Nset := (mapset Nmap).
Instance Nmap_dom {A} : Dom (Nmap A) Nset := mapset_dom.
Instance: FinMapDom N Nmap Nset := mapset_dom_spec.

(** * Fresh numbers *)
Definition Nfresh {A} (m : Nmap A) : N :=
  match m with NMap None _ => 0 | NMap _ m => Npos (Pfresh m) end.
Lemma Nfresh_fresh {A} (m : Nmap A) : m !! Nfresh m = None.
Proof. destruct m as [[]]. apply Pfresh_fresh. done. Qed. 

Instance Nset_fresh : Fresh N Nset := λ X,
  let (m) := X in Nfresh m.
Instance Nset_fresh_spec : FreshSpec N Nset.
Proof.
  split.
  - apply _.
  - intros X Y; rewrite <-elem_of_equiv_L. by intros ->.
  - unfold elem_of, mapset_elem_of, fresh; intros [m]; simpl.
    by rewrite Nfresh_fresh.
Qed.
