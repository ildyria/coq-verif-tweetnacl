(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements finite maps and finite sets with keys of any countable
type. The implementation is based on [Pmap]s, radix-2 search trees. *)
From stdpp Require Export countable fin_maps fin_map_dom.
From stdpp Require Import pmap mapset set.
Set Default Proof Using "Type".

(** * The data structure *)
(** We pack a [Pmap] together with a proof that ensures that all keys correspond
to codes of actual elements of the countable type. *)
Definition gmap_wf `{Countable K} {A} : Pmap A → Prop :=
  map_Forall (λ p _, encode <$> decode p = Some p).
Record gmap K `{Countable K} A := GMap {
  gmap_car : Pmap A;
  gmap_prf : bool_decide (gmap_wf gmap_car)
}.
Arguments GMap {_ _ _ _} _ _ : assert.
Arguments gmap_car {_ _ _ _} _ : assert.
Lemma gmap_eq `{Countable K} {A} (m1 m2 : gmap K A) :
  m1 = m2 ↔ gmap_car m1 = gmap_car m2.
Proof.
  split; [by intros ->|intros]. destruct m1, m2; simplify_eq/=.
  f_equal; apply proof_irrel.
Qed.
Instance gmap_eq_eq `{Countable K, EqDecision A} : EqDecision (gmap K A).
Proof.
 refine (λ m1 m2, cast_if (decide (gmap_car m1 = gmap_car m2)));
  abstract (by rewrite gmap_eq).
Defined.

(** * Operations on the data structure *)
Instance gmap_lookup `{Countable K} {A} : Lookup K A (gmap K A) := λ i m,
  let (m,_) := m in m !! encode i.
Instance gmap_empty `{Countable K} {A} : Empty (gmap K A) := GMap ∅ I.
Global Opaque gmap_empty.
Lemma gmap_partial_alter_wf `{Countable K} {A} (f : option A → option A) m i :
  gmap_wf m → gmap_wf (partial_alter f (encode i) m).
Proof.
  intros Hm p x. destruct (decide (encode i = p)) as [<-|?].
  - rewrite decode_encode; eauto.
  - rewrite lookup_partial_alter_ne by done. by apply Hm.
Qed.
Instance gmap_partial_alter `{Countable K} {A} :
    PartialAlter K A (gmap K A) := λ f i m,
  let (m,Hm) := m in GMap (partial_alter f (encode i) m)
    (bool_decide_pack _ (gmap_partial_alter_wf f m i
    (bool_decide_unpack _ Hm))).
Lemma gmap_fmap_wf `{Countable K} {A B} (f : A → B) m :
  gmap_wf m → gmap_wf (f <$> m).
Proof. intros ? p x. rewrite lookup_fmap, fmap_Some; intros (?&?&?); eauto. Qed.
Instance gmap_fmap `{Countable K} : FMap (gmap K) := λ A B f m,
  let (m,Hm) := m in GMap (f <$> m)
    (bool_decide_pack _ (gmap_fmap_wf f m (bool_decide_unpack _ Hm))).
Lemma gmap_omap_wf `{Countable K} {A B} (f : A → option B) m :
  gmap_wf m → gmap_wf (omap f m).
Proof. intros ? p x; rewrite lookup_omap, bind_Some; intros (?&?&?); eauto. Qed.
Instance gmap_omap `{Countable K} : OMap (gmap K) := λ A B f m,
  let (m,Hm) := m in GMap (omap f m)
    (bool_decide_pack _ (gmap_omap_wf f m (bool_decide_unpack _ Hm))).
Lemma gmap_merge_wf `{Countable K} {A B C}
    (f : option A → option B → option C) m1 m2 :
  let f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end in
  gmap_wf m1 → gmap_wf m2 → gmap_wf (merge f' m1 m2).
Proof.
  intros f' Hm1 Hm2 p z; rewrite lookup_merge by done; intros.
  destruct (m1 !! _) eqn:?, (m2 !! _) eqn:?; naive_solver.
Qed.
Instance gmap_merge `{Countable K} : Merge (gmap K) := λ A B C f m1 m2,
  let (m1,Hm1) := m1 in let (m2,Hm2) := m2 in
  let f' o1 o2 := match o1, o2 with None, None => None | _, _ => f o1 o2 end in
  GMap (merge f' m1 m2) (bool_decide_pack _ (gmap_merge_wf f _ _
    (bool_decide_unpack _ Hm1) (bool_decide_unpack _ Hm2))).
Instance gmap_to_list `{Countable K} {A} : FinMapToList K A (gmap K A) := λ m,
  let (m,_) := m in omap (λ ix : positive * A,
    let (i,x) := ix in (,x) <$> decode i) (map_to_list m).

(** * Instantiation of the finite map interface *)
Instance gmap_finmap `{Countable K} : FinMap K (gmap K).
Proof.
  split.
  - unfold lookup; intros A [m1 Hm1] [m2 Hm2] Hm.
    apply gmap_eq, map_eq; intros i; simpl in *.
    apply bool_decide_unpack in Hm1; apply bool_decide_unpack in Hm2.
    apply option_eq; intros x; split; intros Hi.
    + pose proof (Hm1 i x Hi); simpl in *.
      by destruct (decode i); simplify_eq/=; rewrite <-Hm.
    + pose proof (Hm2 i x Hi); simpl in *.
      by destruct (decode i); simplify_eq/=; rewrite Hm.
  - done.
  - intros A f [m Hm] i; apply (lookup_partial_alter f m).
  - intros A f [m Hm] i j Hs; apply (lookup_partial_alter_ne f m).
    by contradict Hs; apply (inj encode).
  - intros A B f [m Hm] i; apply (lookup_fmap f m).
  - intros A [m Hm]; unfold map_to_list; simpl.
    apply bool_decide_unpack, map_Forall_to_list in Hm; revert Hm.
    induction (NoDup_map_to_list m) as [|[p x] l Hpx];
      inversion 1 as [|??? Hm']; simplify_eq/=; [by constructor|].
    destruct (decode p) as [i|] eqn:?; simplify_eq/=; constructor; eauto.
    rewrite elem_of_list_omap; intros ([p' x']&?&?); simplify_eq/=.
    feed pose proof (proj1 (Forall_forall _ _) Hm' (p',x')); simpl in *; auto.
    by destruct (decode p') as [i'|]; simplify_eq/=.
  - intros A [m Hm] i x; unfold map_to_list, lookup; simpl.
    apply bool_decide_unpack in Hm; rewrite elem_of_list_omap; split.
    + intros ([p' x']&Hp'&?); apply elem_of_map_to_list in Hp'.
      feed pose proof (Hm p' x'); simpl in *; auto.
      by destruct (decode p') as [i'|] eqn:?; simplify_eq/=.
    + intros; exists (encode i,x); simpl.
      by rewrite elem_of_map_to_list, decode_encode.
  - intros A B f [m Hm] i; apply (lookup_omap f m).
  - intros A B C f ? [m1 Hm1] [m2 Hm2] i; unfold merge, lookup; simpl.
    set (f' o1 o2 := match o1, o2 with None,None => None | _, _ => f o1 o2 end).
    by rewrite lookup_merge by done; destruct (m1 !! _), (m2 !! _).
Qed.

Program Instance gmap_countable
    `{Countable K, Countable A} : Countable (gmap K A) := {
  encode m := encode (map_to_list m : list (K * A));
  decode p := map_of_list <$> decode p
}.
Next Obligation.
  intros K ?? A ?? m; simpl. rewrite decode_encode; simpl.
  by rewrite map_of_to_list.
Qed.

(** * Curry and uncurry *)
Definition gmap_curry `{Countable K1, Countable K2} {A} :
    gmap K1 (gmap K2 A) → gmap (K1 * K2) A :=
  map_fold (λ i1 m' macc,
    map_fold (λ i2 x, <[(i1,i2):=x]>) macc m') ∅.
Definition gmap_uncurry `{Countable K1, Countable K2} {A} :
    gmap (K1 * K2) A → gmap K1 (gmap K2 A) :=
  map_fold (λ ii x, let '(i1,i2) := ii in
    partial_alter (Some ∘ <[i2:=x]> ∘ from_option id ∅) i1) ∅.

Section curry_uncurry.
  Context `{Countable K1, Countable K2} {A : Type}.

  (* FIXME: the type annotations `option (gmap K2 A)` are silly. Maybe these are
  a consequence of Coq bug #5735 *)
  Lemma lookup_gmap_curry (m : gmap K1 (gmap K2 A)) i j :
    gmap_curry m !! (i,j) = (m !! i : option (gmap K2 A)) ≫= (!! j).
  Proof.
    apply (map_fold_ind (λ mr m, mr !! (i,j) = m !! i ≫= (!! j))).
    { by rewrite !lookup_empty. }
    clear m; intros i' m2 m m12 Hi' IH.
    apply (map_fold_ind (λ m2r m2, m2r !! (i,j) = <[i':=m2]> m !! i ≫= (!! j))).
    { rewrite IH. destruct (decide (i' = i)) as [->|].
      - rewrite lookup_insert, Hi'; simpl; by rewrite lookup_empty.
      - by rewrite lookup_insert_ne by done. }
    intros j' y m2' m12' Hj' IH'. destruct (decide (i = i')) as [->|].
    - rewrite lookup_insert; simpl. destruct (decide (j = j')) as [->|].
      + by rewrite !lookup_insert.
      + by rewrite !lookup_insert_ne, IH', lookup_insert by congruence.
    - by rewrite !lookup_insert_ne, IH', lookup_insert_ne by congruence.
  Qed.

  Lemma lookup_gmap_uncurry (m : gmap (K1 * K2) A) i j :
    (gmap_uncurry m !! i : option (gmap K2 A)) ≫= (!! j) = m !! (i, j).
  Proof.
    apply (map_fold_ind (λ mr m, mr !! i ≫= (!! j) = m !! (i, j))).
    { by rewrite !lookup_empty. }
    clear m; intros [i' j'] x m12 mr Hij' IH.
    destruct (decide (i = i')) as [->|].
    - rewrite lookup_partial_alter. destruct (decide (j = j')) as [->|].
      + destruct (mr !! i'); simpl; by rewrite !lookup_insert.
      + destruct (mr !! i'); simpl; by rewrite !lookup_insert_ne by congruence.
    - by rewrite lookup_partial_alter_ne, lookup_insert_ne by congruence.
  Qed.

  Lemma lookup_gmap_uncurry_None (m : gmap (K1 * K2) A) i :
    gmap_uncurry m !! i = None ↔ (∀ j, m !! (i, j) = None).
  Proof.
    apply (map_fold_ind (λ mr m, mr !! i = None ↔ (∀ j, m !! (i, j) = None)));
      [done|].
    clear m; intros [i' j'] x m12 mr Hij' IH.
    destruct (decide (i = i')) as [->|].
    - split; [by rewrite lookup_partial_alter|].
      intros Hi. specialize (Hi j'). by rewrite lookup_insert in Hi.
    - rewrite lookup_partial_alter_ne, IH; [|done]. apply forall_proper.
      intros j. rewrite lookup_insert_ne; [done|congruence].
  Qed.

  Lemma gmap_curry_uncurry (m : gmap (K1 * K2) A) :
    gmap_curry (gmap_uncurry m) = m.
  Proof.
   apply map_eq; intros [i j]. by rewrite lookup_gmap_curry, lookup_gmap_uncurry.
  Qed.

  Lemma gmap_uncurry_non_empty (m : gmap (K1 * K2) A) i x :
    gmap_uncurry m !! i = Some x → x ≠ ∅.
  Proof.
    intros Hm ->. eapply eq_None_not_Some; [|by eexists].
    eapply lookup_gmap_uncurry_None; intros j.
    by rewrite <-lookup_gmap_uncurry, Hm.
  Qed.

  Lemma gmap_uncurry_curry_non_empty (m : gmap K1 (gmap K2 A)) :
    (∀ i x, m !! i = Some x → x ≠ ∅) →
    gmap_uncurry (gmap_curry m) = m.
  Proof.
    intros Hne. apply map_eq; intros i. destruct (m !! i) as [m2|] eqn:Hm.
    - destruct (gmap_uncurry (gmap_curry m) !! i) as [m2'|] eqn:Hcurry.
      + f_equal. apply map_eq. intros j.
        trans ((gmap_uncurry (gmap_curry m) !! i : option (gmap _ _)) ≫= (!! j)).
        { by rewrite Hcurry. }
        by rewrite lookup_gmap_uncurry, lookup_gmap_curry, Hm.
      + rewrite lookup_gmap_uncurry_None in Hcurry.
        exfalso; apply (Hne i m2), map_eq; [done|intros j].
        by rewrite lookup_empty, <-(Hcurry j), lookup_gmap_curry, Hm.
   - apply lookup_gmap_uncurry_None; intros j. by rewrite lookup_gmap_curry, Hm.
  Qed.
End curry_uncurry.

(** * Finite sets *)
Notation gset K := (mapset (gmap K)).
Instance gset_dom `{Countable K} {A} : Dom (gmap K A) (gset K) := mapset_dom.
Instance gset_dom_spec `{Countable K} :
  FinMapDom K (gmap K) (gset K) := mapset_dom_spec.

Definition of_gset `{Countable A} (X : gset A) : set A := mkSet (λ x, x ∈ X).
Lemma elem_of_of_gset `{Countable A} (X : gset A) x : x ∈ of_gset X ↔ x ∈ X.
Proof. done. Qed.

Definition to_gmap `{Countable K} {A} (x : A) (X : gset K) : gmap K A :=
  (λ _, x) <$> mapset_car X.

Lemma lookup_to_gmap `{Countable K} {A} (x : A) (X : gset K) i :
  to_gmap x X !! i = guard (i ∈ X); Some x.
Proof.
  destruct X as [X]; unfold to_gmap, elem_of, mapset_elem_of; simpl.
  rewrite lookup_fmap.
  case_option_guard; destruct (X !! i) as [[]|]; naive_solver.
Qed.
Lemma lookup_to_gmap_Some `{Countable K} {A} (x : A) (X : gset K) i y :
  to_gmap x X !! i = Some y ↔ i ∈ X ∧ x = y.
Proof. rewrite lookup_to_gmap. simplify_option_eq; naive_solver. Qed.
Lemma lookup_to_gmap_None `{Countable K} {A} (x : A) (X : gset K) i :
  to_gmap x X !! i = None ↔ i ∉ X.
Proof. rewrite lookup_to_gmap. simplify_option_eq; naive_solver. Qed.

Lemma to_gmap_empty `{Countable K} {A} (x : A) : to_gmap x ∅ = ∅.
Proof. apply fmap_empty. Qed.
Lemma to_gmap_union_singleton `{Countable K} {A} (x : A) i Y :
  to_gmap x ({[ i ]} ∪ Y) = <[i:=x]>(to_gmap x Y).
Proof.
  apply map_eq; intros j; apply option_eq; intros y.
  rewrite lookup_insert_Some, !lookup_to_gmap_Some, elem_of_union,
    elem_of_singleton; destruct (decide (i = j)); intuition.
Qed.

Lemma fmap_to_gmap `{Countable K} {A B} (f : A → B) (X : gset K) (x : A) :
  f <$> to_gmap x X = to_gmap (f x) X.
Proof.
  apply map_eq; intros j. rewrite lookup_fmap, !lookup_to_gmap.
  by simplify_option_eq.
Qed.
Lemma to_gmap_dom `{Countable K} {A B} (m : gmap K A) (y : B) :
  to_gmap y (dom _ m) = const y <$> m.
Proof.
  apply map_eq; intros j. rewrite lookup_fmap, lookup_to_gmap.
  destruct (m !! j) as [x|] eqn:?.
  - by rewrite option_guard_True by (rewrite elem_of_dom; eauto).
  - by rewrite option_guard_False by (rewrite not_elem_of_dom; eauto).
Qed.

(** * Fresh elements *)
(* This is pretty ad-hoc and just for the case of [gset positive]. We need a
notion of countable non-finite types to generalize this. *)
Instance gset_positive_fresh : Fresh positive (gset positive) := λ X,
  let 'Mapset (GMap m _) := X in fresh (dom Pset m).
Instance gset_positive_fresh_spec : FreshSpec positive (gset positive).
Proof.
  split.
  - apply _.
  - by intros X Y; rewrite <-elem_of_equiv_L; intros ->.
  - intros [[m Hm]]; unfold fresh; simpl.
    by intros ?; apply (is_fresh (dom Pset m)), elem_of_dom_2 with ().
Qed.
