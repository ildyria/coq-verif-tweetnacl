(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file provides an axiomatization of the domain function of finite
maps. We provide such an axiomatization, instead of implementing the domain
function in a generic way, to allow more efficient implementations. *)
From stdpp Require Export collections fin_maps.
Set Default Proof Using "Type*".

Class FinMapDom K M D `{∀ A, Dom (M A) D, FMap M,
    ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A, PartialAlter K A (M A),
    OMap M, Merge M, ∀ A, FinMapToList K A (M A), EqDecision K,
    ElemOf K D, Empty D, Singleton K D,
    Union D, Intersection D, Difference D} := {
  finmap_dom_map :>> FinMap K M;
  finmap_dom_collection :>> Collection K D;
  elem_of_dom {A} (m : M A) i : i ∈ dom D m ↔ is_Some (m !! i)
}.

Section fin_map_dom.
Context `{FinMapDom K M D}.

Lemma dom_map_filter {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m : M A):
  dom D (filter P m) ⊆ dom D m.
Proof.
  intros ?. rewrite 2!elem_of_dom.
  destruct 1 as [?[Eq _]%map_filter_lookup_Some]. by eexists.
Qed.

Lemma elem_of_dom_2 {A} (m : M A) i x : m !! i = Some x → i ∈ dom D m.
Proof. rewrite elem_of_dom; eauto. Qed.
Lemma not_elem_of_dom {A} (m : M A) i : i ∉ dom D m ↔ m !! i = None.
Proof. by rewrite elem_of_dom, eq_None_not_Some. Qed.
Lemma subseteq_dom {A} (m1 m2 : M A) : m1 ⊆ m2 → dom D m1 ⊆ dom D m2.
Proof.
  rewrite map_subseteq_spec.
  intros ??. rewrite !elem_of_dom. inversion 1; eauto.
Qed.
Lemma subset_dom {A} (m1 m2 : M A) : m1 ⊂ m2 → dom D m1 ⊂ dom D m2.
Proof.
  intros [Hss1 Hss2]; split; [by apply subseteq_dom |].
  contradict Hss2. rewrite map_subseteq_spec. intros i x Hi.
  specialize (Hss2 i). rewrite !elem_of_dom in Hss2.
  destruct Hss2; eauto. by simplify_map_eq.
Qed.
Lemma dom_empty {A} : dom D (@empty (M A) _) ≡ ∅.
Proof.
  intros x. rewrite elem_of_dom, lookup_empty, <-not_eq_None_Some. set_solver.
Qed.
Lemma dom_empty_inv {A} (m : M A) : dom D m ≡ ∅ → m = ∅.
Proof.
  intros E. apply map_empty. intros. apply not_elem_of_dom.
  rewrite E. set_solver.
Qed.
Lemma dom_alter {A} f (m : M A) i : dom D (alter f i m) ≡ dom D m.
Proof.
  apply elem_of_equiv; intros j; rewrite !elem_of_dom; unfold is_Some.
  destruct (decide (i = j)); simplify_map_eq/=; eauto.
  destruct (m !! j); naive_solver.
Qed.
Lemma dom_insert {A} (m : M A) i x : dom D (<[i:=x]>m) ≡ {[ i ]} ∪ dom D m.
Proof.
  apply elem_of_equiv. intros j. rewrite elem_of_union, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_insert_Some.
  destruct (decide (i = j)); set_solver.
Qed.
Lemma dom_insert_subseteq {A} (m : M A) i x : dom D m ⊆ dom D (<[i:=x]>m).
Proof. rewrite (dom_insert _). set_solver. Qed.
Lemma dom_insert_subseteq_compat_l {A} (m : M A) i x X :
  X ⊆ dom D m → X ⊆ dom D (<[i:=x]>m).
Proof. intros. trans (dom D m); eauto using dom_insert_subseteq. Qed.
Lemma dom_singleton {A} (i : K) (x : A) : dom D ({[i := x]} : M A) ≡ {[ i ]}.
Proof. rewrite <-insert_empty, dom_insert, dom_empty; set_solver. Qed.
Lemma dom_delete {A} (m : M A) i : dom D (delete i m) ≡ dom D m ∖ {[ i ]}.
Proof.
  apply elem_of_equiv. intros j. rewrite elem_of_difference, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_delete_Some. set_solver.
Qed.
Lemma delete_partial_alter_dom {A} (m : M A) i f :
  i ∉ dom D m → delete i (partial_alter f i m) = m.
Proof. rewrite not_elem_of_dom. apply delete_partial_alter. Qed.
Lemma delete_insert_dom {A} (m : M A) i x :
  i ∉ dom D m → delete i (<[i:=x]>m) = m.
Proof. rewrite not_elem_of_dom. apply delete_insert. Qed.
Lemma map_disjoint_dom {A} (m1 m2 : M A) : m1 ##ₘ m2 ↔ dom D m1 ## dom D m2.
Proof.
  rewrite map_disjoint_spec, elem_of_disjoint.
  setoid_rewrite elem_of_dom. unfold is_Some. naive_solver.
Qed.
Lemma map_disjoint_dom_1 {A} (m1 m2 : M A) : m1 ##ₘ m2 → dom D m1 ## dom D m2.
Proof. apply map_disjoint_dom. Qed.
Lemma map_disjoint_dom_2 {A} (m1 m2 : M A) : dom D m1 ## dom D m2 → m1 ##ₘ m2.
Proof. apply map_disjoint_dom. Qed.
Lemma dom_union {A} (m1 m2 : M A) : dom D (m1 ∪ m2) ≡ dom D m1 ∪ dom D m2.
Proof.
  apply elem_of_equiv. intros i. rewrite elem_of_union, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_union_Some_raw.
  destruct (m1 !! i); naive_solver.
Qed.
Lemma dom_intersection {A} (m1 m2: M A) : dom D (m1 ∩ m2) ≡ dom D m1 ∩ dom D m2.
Proof.
  apply elem_of_equiv. intros i. rewrite elem_of_intersection, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_intersection_Some. naive_solver.
Qed.
Lemma dom_difference {A} (m1 m2 : M A) : dom D (m1 ∖ m2) ≡ dom D m1 ∖ dom D m2.
Proof.
  apply elem_of_equiv. intros i. rewrite elem_of_difference, !elem_of_dom.
  unfold is_Some. setoid_rewrite lookup_difference_Some.
  destruct (m2 !! i); naive_solver.
Qed.
Lemma dom_fmap {A B} (f : A → B) (m : M A) : dom D (f <$> m) ≡ dom D m.
Proof.
  apply elem_of_equiv. intros i.
  rewrite !elem_of_dom, lookup_fmap, <-!not_eq_None_Some.
  destruct (m !! i); naive_solver.
Qed.
Lemma dom_finite {A} (m : M A) : set_finite (dom D m).
Proof.
  induction m using map_ind; rewrite ?dom_empty, ?dom_insert;
    eauto using (empty_finite (C:=D)), (union_finite (C:=D)),
    (singleton_finite (C:=D)).
Qed.

Context `{!LeibnizEquiv D}.
Lemma dom_empty_L {A} : dom D (@empty (M A) _) = ∅.
Proof. unfold_leibniz; apply dom_empty. Qed.
Lemma dom_empty_inv_L {A} (m : M A) : dom D m = ∅ → m = ∅.
Proof. by intros; apply dom_empty_inv; unfold_leibniz. Qed.
Lemma dom_alter_L {A} f (m : M A) i : dom D (alter f i m) = dom D m.
Proof. unfold_leibniz; apply dom_alter. Qed.
Lemma dom_insert_L {A} (m : M A) i x : dom D (<[i:=x]>m) = {[ i ]} ∪ dom D m.
Proof. unfold_leibniz; apply dom_insert. Qed.
Lemma dom_singleton_L {A} (i : K) (x : A) : dom D ({[i := x]} : M A) = {[ i ]}.
Proof. unfold_leibniz; apply dom_singleton. Qed.
Lemma dom_delete_L {A} (m : M A) i : dom D (delete i m) = dom D m ∖ {[ i ]}.
Proof. unfold_leibniz; apply dom_delete. Qed.
Lemma dom_union_L {A} (m1 m2 : M A) : dom D (m1 ∪ m2) = dom D m1 ∪ dom D m2.
Proof. unfold_leibniz; apply dom_union. Qed.
Lemma dom_intersection_L {A} (m1 m2 : M A) :
  dom D (m1 ∩ m2) = dom D m1 ∩ dom D m2.
Proof. unfold_leibniz; apply dom_intersection. Qed.
Lemma dom_difference_L {A} (m1 m2 : M A) : dom D (m1 ∖ m2) = dom D m1 ∖ dom D m2.
Proof. unfold_leibniz; apply dom_difference. Qed.
Lemma dom_fmap_L {A B} (f : A → B) (m : M A) : dom D (f <$> m) = dom D m.
Proof. unfold_leibniz; apply dom_fmap. Qed.
End fin_map_dom.
