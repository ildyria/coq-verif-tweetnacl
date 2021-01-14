(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on the option
data type that are not in the Coq standard library. *)
From stdpp Require Export tactics.
Set Default Proof Using "Type".

Inductive option_reflect {A} (P : A → Prop) (Q : Prop) : option A → Type :=
  | ReflectSome x : P x → option_reflect P Q (Some x)
  | ReflectNone : Q → option_reflect P Q None.

(** * General definitions and theorems *)
(** Basic properties about equality. *)
Lemma None_ne_Some {A} (x : A) : None ≠ Some x.
Proof. congruence. Qed.
Lemma Some_ne_None {A} (x : A) : Some x ≠ None.
Proof. congruence. Qed.
Lemma eq_None_ne_Some {A} (mx : option A) x : mx = None → mx ≠ Some x.
Proof. congruence. Qed.
Instance Some_inj {A} : Inj (=) (=) (@Some A).
Proof. congruence. Qed.

(** The [from_option] is the eliminator for option. *)
Definition from_option {A B} (f : A → B) (y : B) (mx : option A) : B :=
  match mx with None => y | Some x => f x end.
Instance: Params (@from_option) 3.
Arguments from_option {_ _} _ _ !_ / : assert.

(* The eliminator again, but with the arguments in different order, which is
sometimes more convenient. *)
Notation default y mx f := (from_option f y mx) (only parsing).

(** An alternative, but equivalent, definition of equality on the option
data type. This theorem is useful to prove that two options are the same. *)
Lemma option_eq {A} (mx my: option A): mx = my ↔ ∀ x, mx = Some x ↔ my = Some x.
Proof. split; [by intros; by subst |]. destruct mx, my; naive_solver. Qed.
Lemma option_eq_1 {A} (mx my: option A) x : mx = my → mx = Some x → my = Some x.
Proof. congruence. Qed.
Lemma option_eq_1_alt {A} (mx my : option A) x :
  mx = my → my = Some x → mx = Some x.
Proof. congruence. Qed.

Definition is_Some {A} (mx : option A) := ∃ x, mx = Some x.
Instance: Params (@is_Some) 1.

Lemma is_Some_alt {A} (mx : option A) :
  is_Some mx ↔ match mx with Some _ => True | None => False end.
Proof. unfold is_Some. destruct mx; naive_solver. Qed.

Lemma mk_is_Some {A} (mx : option A) x : mx = Some x → is_Some mx.
Proof. intros; red; subst; eauto. Qed.
Hint Resolve mk_is_Some.
Lemma is_Some_None {A} : ¬is_Some (@None A).
Proof. by destruct 1. Qed.
Hint Resolve is_Some_None.

Lemma eq_None_not_Some {A} (mx : option A) : mx = None ↔ ¬is_Some mx.
Proof. rewrite is_Some_alt; destruct mx; naive_solver. Qed.
Lemma not_eq_None_Some {A} (mx : option A) : mx ≠ None ↔ is_Some mx.
Proof. rewrite is_Some_alt; destruct mx; naive_solver. Qed.

Instance is_Some_pi {A} (mx : option A) : ProofIrrel (is_Some mx).
Proof.
  set (P (mx : option A) := match mx with Some _ => True | _ => False end).
  set (f mx := match mx return P mx → is_Some mx with
    Some _ => λ _, ex_intro _ _ eq_refl | None => False_rect _ end).
  set (g mx (H : is_Some mx) :=
    match H return P mx with ex_intro _ _ p => eq_rect _ _ I _ (eq_sym p) end).
  assert (∀ mx H, f mx (g mx H) = H) as f_g by (by intros ? [??]; subst).
  intros p1 p2. rewrite <-(f_g _ p1), <-(f_g _ p2). by destruct mx, p1.
Qed.

Instance is_Some_dec {A} (mx : option A) : Decision (is_Some mx) :=
  match mx with
  | Some x => left (ex_intro _ x eq_refl)
  | None => right is_Some_None
  end.

Definition is_Some_proj {A} {mx : option A} : is_Some mx → A :=
  match mx with Some x => λ _, x | None => False_rect _ ∘ is_Some_None end.

Definition Some_dec {A} (mx : option A) : { x | mx = Some x } + { mx = None } :=
  match mx return { x | mx = Some x } + { mx = None } with
  | Some x => inleft (x ↾ eq_refl _)
  | None => inright eq_refl
  end.

(** Lifting a relation point-wise to option *)
Inductive option_Forall2 {A B} (R: A → B → Prop) : option A → option B → Prop :=
  | Some_Forall2 x y : R x y → option_Forall2 R (Some x) (Some y)
  | None_Forall2 : option_Forall2 R None None.
Definition option_relation {A B} (R: A → B → Prop) (P: A → Prop) (Q: B → Prop)
    (mx : option A) (my : option B) : Prop :=
  match mx, my with
  | Some x, Some y => R x y
  | Some x, None => P x
  | None, Some y => Q y
  | None, None => True
  end.

Section Forall2.
  Context {A} (R : relation A).

  Global Instance option_Forall2_refl : Reflexive R → Reflexive (option_Forall2 R).
  Proof. intros ? [?|]; by constructor. Qed.
  Global Instance option_Forall2_sym : Symmetric R → Symmetric (option_Forall2 R).
  Proof. destruct 2; by constructor. Qed.
  Global Instance option_Forall2_trans : Transitive R → Transitive (option_Forall2 R).
  Proof. destruct 2; inversion_clear 1; constructor; etrans; eauto. Qed.
  Global Instance option_Forall2_equiv : Equivalence R → Equivalence (option_Forall2 R).
  Proof. destruct 1; split; apply _. Qed.
End Forall2.

(** Setoids *)
Instance option_equiv `{Equiv A} : Equiv (option A) := option_Forall2 (≡).

Section setoids.
  Context `{Equiv A}.
  Implicit Types mx my : option A.

  Lemma equiv_option_Forall2 mx my : mx ≡ my ↔ option_Forall2 (≡) mx my.
  Proof. done. Qed.

  Global Instance option_equivalence :
    Equivalence ((≡) : relation A) → Equivalence ((≡) : relation (option A)).
  Proof. apply _. Qed.
  Global Instance Some_proper : Proper ((≡) ==> (≡)) (@Some A).
  Proof. by constructor. Qed.
  Global Instance Some_equiv_inj : Inj (≡) (≡) (@Some A).
  Proof. by inversion_clear 1. Qed.
  Global Instance option_leibniz `{!LeibnizEquiv A} : LeibnizEquiv (option A).
  Proof. intros x y; destruct 1; f_equal; by apply leibniz_equiv. Qed.

  Lemma equiv_None mx : mx ≡ None ↔ mx = None.
  Proof. split; [by inversion_clear 1|intros ->; constructor]. Qed.
  Lemma equiv_Some_inv_l mx my x :
    mx ≡ my → mx = Some x → ∃ y, my = Some y ∧ x ≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma equiv_Some_inv_r mx my y :
    mx ≡ my → my = Some y → ∃ x, mx = Some x ∧ x ≡ y.
  Proof. destruct 1; naive_solver. Qed.
  Lemma equiv_Some_inv_l' my x : Some x ≡ my → ∃ x', Some x' = my ∧ x ≡ x'.
  Proof. intros ?%(equiv_Some_inv_l _ _ x); naive_solver. Qed.
  Lemma equiv_Some_inv_r' `{!Equivalence ((≡) : relation A)} mx y :
    mx ≡ Some y → ∃ y', mx = Some y' ∧ y ≡ y'.
  Proof. intros ?%(equiv_Some_inv_r _ _ y); naive_solver. Qed.

  Global Instance is_Some_proper : Proper ((≡) ==> iff) (@is_Some A).
  Proof. inversion_clear 1; split; eauto. Qed.
  Global Instance from_option_proper {B} (R : relation B) (f : A → B) :
    Proper ((≡) ==> R) f → Proper (R ==> (≡) ==> R) (from_option f).
  Proof. destruct 3; simpl; auto. Qed.
End setoids.

Typeclasses Opaque option_equiv.

(** Equality on [option] is decidable. *)
Instance option_eq_None_dec {A} (mx : option A) : Decision (mx = None) :=
  match mx with Some _ => right (Some_ne_None _) | None => left eq_refl end.
Instance option_None_eq_dec {A} (mx : option A) : Decision (None = mx) :=
  match mx with Some _ => right (None_ne_Some _) | None => left eq_refl end.
Instance option_eq_dec `{dec : EqDecision A} : EqDecision (option A).
Proof.
 refine (λ mx my,
  match mx, my with
  | Some x, Some y => cast_if (decide (x = y))
  | None, None => left _ | _, _ => right _
  end); clear dec; abstract congruence.
Defined.

(** * Monadic operations *)
Instance option_ret: MRet option := @Some.
Instance option_bind: MBind option := λ A B f mx,
  match mx with Some x => f x | None => None end.
Instance option_join: MJoin option := λ A mmx,
  match mmx with Some mx => mx | None => None end.
Instance option_fmap: FMap option := @option_map.
Instance option_guard: MGuard option := λ P dec A f,
  match dec with left H => f H | _ => None end.

Lemma fmap_is_Some {A B} (f : A → B) mx : is_Some (f <$> mx) ↔ is_Some mx.
Proof. unfold is_Some; destruct mx; naive_solver. Qed.
Lemma fmap_Some {A B} (f : A → B) mx y :
  f <$> mx = Some y ↔ ∃ x, mx = Some x ∧ y = f x.
Proof. destruct mx; naive_solver. Qed.
Lemma fmap_Some_equiv {A B} `{Equiv B} `{!Equivalence ((≡) : relation B)}
      (f : A → B) mx y :
  f <$> mx ≡ Some y ↔ ∃ x, mx = Some x ∧ y ≡ f x.
Proof.
  destruct mx; simpl; split.
  - intros ?%Some_equiv_inj. eauto.
  - intros (? & ->%Some_inj & ?). constructor. done.
  - intros ?%symmetry%equiv_None. done.
  - intros (? & ? & ?). done.
Qed.
Lemma fmap_Some_equiv_1 {A B} `{Equiv B} `{!Equivalence ((≡) : relation B)}
      (f : A → B) mx y :
  f <$> mx ≡ Some y → ∃ x, mx = Some x ∧ y ≡ f x.
Proof. by rewrite fmap_Some_equiv. Qed.
Lemma fmap_None {A B} (f : A → B) mx : f <$> mx = None ↔ mx = None.
Proof. by destruct mx. Qed.
Lemma option_fmap_id {A} (mx : option A) : id <$> mx = mx.
Proof. by destruct mx. Qed.
Lemma option_fmap_compose {A B} (f : A → B) {C} (g : B → C) mx :
  g ∘ f <$> mx = g <$> (f <$> mx).
Proof. by destruct mx. Qed.
Lemma option_fmap_ext {A B} (f g : A → B) mx :
  (∀ x, f x = g x) → f <$> mx = g <$> mx.
Proof. intros; destruct mx; f_equal/=; auto. Qed.
Lemma option_fmap_equiv_ext `{Equiv A, Equiv B} (f g : A → B) (mx : option A) :
  (∀ x, f x ≡ g x) → f <$> mx ≡ g <$> mx.
Proof. destruct mx; constructor; auto. Qed.
Lemma option_fmap_bind {A B C} (f : A → B) (g : B → option C) mx :
  (f <$> mx) ≫= g = mx ≫= g ∘ f.
Proof. by destruct mx. Qed.
Lemma option_bind_assoc {A B C} (f : A → option B)
  (g : B → option C) (mx : option A) : (mx ≫= f) ≫= g = mx ≫= (mbind g ∘ f).
Proof. by destruct mx; simpl. Qed.
Lemma option_bind_ext {A B} (f g : A → option B) mx my :
  (∀ x, f x = g x) → mx = my → mx ≫= f = my ≫= g.
Proof. destruct mx, my; naive_solver. Qed.
Lemma option_bind_ext_fun {A B} (f g : A → option B) mx :
  (∀ x, f x = g x) → mx ≫= f = mx ≫= g.
Proof. intros. by apply option_bind_ext. Qed.
Lemma bind_Some {A B} (f : A → option B) (mx : option A) y :
  mx ≫= f = Some y ↔ ∃ x, mx = Some x ∧ f x = Some y.
Proof. destruct mx; naive_solver. Qed.
Lemma bind_None {A B} (f : A → option B) (mx : option A) :
  mx ≫= f = None ↔ mx = None ∨ ∃ x, mx = Some x ∧ f x = None.
Proof. destruct mx; naive_solver. Qed.
Lemma bind_with_Some {A} (mx : option A) : mx ≫= Some = mx.
Proof. by destruct mx. Qed.

Instance option_fmap_proper `{Equiv A, Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡) ==> (≡)) (fmap (M:=option) (A:=A) (B:=B)).
Proof. destruct 2; constructor; auto. Qed.
Instance option_mbind_proper `{Equiv A, Equiv B} :
  Proper (((≡) ==> (≡)) ==> (≡) ==> (≡)) (mbind (M:=option) (A:=A) (B:=B)).
Proof. destruct 2; simpl; try constructor; auto. Qed.
Instance option_mjoin_proper `{Equiv A} :
  Proper ((≡) ==> (≡)) (mjoin (M:=option) (A:=A)).
Proof. destruct 1 as [?? []|]; simpl; by constructor. Qed.

(** ** Inverses of constructors *)
(** We can do this in a fancy way using dependent types, but rewrite does
not particularly like type level reductions. *)
Class Maybe {A B : Type} (c : A → B) :=
  maybe : B → option A.
Arguments maybe {_ _} _ {_} !_ / : assert.
Class Maybe2 {A1 A2 B : Type} (c : A1 → A2 → B) :=
  maybe2 : B → option (A1 * A2).
Arguments maybe2 {_ _ _} _ {_} !_ / : assert.
Class Maybe3 {A1 A2 A3 B : Type} (c : A1 → A2 → A3 → B) :=
  maybe3 : B → option (A1 * A2 * A3).
Arguments maybe3 {_ _ _ _} _ {_} !_ / : assert.
Class Maybe4 {A1 A2 A3 A4 B : Type} (c : A1 → A2 → A3 → A4 → B) :=
  maybe4 : B → option (A1 * A2 * A3 * A4).
Arguments maybe4 {_ _ _ _ _} _ {_} !_ / : assert.

Instance maybe_comp `{Maybe B C c1, Maybe A B c2} : Maybe (c1 ∘ c2) := λ x,
  maybe c1 x ≫= maybe c2.
Arguments maybe_comp _ _ _ _ _ _ _ !_ / : assert.

Instance maybe_inl {A B} : Maybe (@inl A B) := λ xy,
  match xy with inl x => Some x | _ => None end.
Instance maybe_inr {A B} : Maybe (@inr A B) := λ xy,
  match xy with inr y => Some y | _ => None end.
Instance maybe_Some {A} : Maybe (@Some A) := id.
Arguments maybe_Some _ !_ / : assert.

(** * Union, intersection and difference *)
Instance option_union_with {A} : UnionWith A (option A) := λ f mx my,
  match mx, my with
  | Some x, Some y => f x y
  | Some x, None => Some x
  | None, Some y => Some y
  | None, None => None
  end.
Instance option_intersection_with {A} : IntersectionWith A (option A) :=
  λ f mx my, match mx, my with Some x, Some y => f x y | _, _ => None end.
Instance option_difference_with {A} : DifferenceWith A (option A) := λ f mx my,
  match mx, my with
  | Some x, Some y => f x y
  | Some x, None => Some x
  | None, _ => None
  end.
Instance option_union {A} : Union (option A) := union_with (λ x _, Some x).

Lemma option_union_Some {A} (mx my : option A) z :
  mx ∪ my = Some z → mx = Some z ∨ my = Some z.
Proof. destruct mx, my; naive_solver. Qed.

Class DiagNone {A B C} (f : option A → option B → option C) :=
  diag_none : f None None = None.

Section union_intersection_difference.
  Context {A} (f : A → A → option A).

  Global Instance union_with_diag_none : DiagNone (union_with f).
  Proof. reflexivity. Qed.
  Global Instance intersection_with_diag_none : DiagNone (intersection_with f).
  Proof. reflexivity. Qed.
  Global Instance difference_with_diag_none : DiagNone (difference_with f).
  Proof. reflexivity. Qed.
  Global Instance union_with_left_id : LeftId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance union_with_right_id : RightId (=) None (union_with f).
  Proof. by intros [?|]. Qed.
  Global Instance union_with_comm :
    Comm (=) f → Comm (=) (union_with (M:=option A) f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(comm f). Qed.
  Global Instance intersection_with_left_ab : LeftAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance intersection_with_right_ab : RightAbsorb (=) None (intersection_with f).
  Proof. by intros [?|]. Qed.
  Global Instance difference_with_comm :
    Comm (=) f → Comm (=) (intersection_with (M:=option A) f).
  Proof. by intros ? [?|] [?|]; compute; rewrite 1?(comm f). Qed.
  Global Instance difference_with_right_id : RightId (=) None (difference_with f).
  Proof. by intros [?|]. Qed.
End union_intersection_difference.

(** * Tactics *)
Tactic Notation "case_option_guard" "as" ident(Hx) :=
  match goal with
  | H : context C [@mguard option _ ?P ?dec] |- _ =>
    change (@mguard option _ P dec) with (λ A (f : P → option A),
      match @decide P dec with left H' => f H' | _ => None end) in *;
    destruct_decide (@decide P dec) as Hx
  | |- context C [@mguard option _ ?P ?dec] =>
    change (@mguard option _ P dec) with (λ A (f : P → option A),
      match @decide P dec with left H' => f H' | _ => None end) in *;
    destruct_decide (@decide P dec) as Hx
  end.
Tactic Notation "case_option_guard" :=
  let H := fresh in case_option_guard as H.

Lemma option_guard_True {A} P `{Decision P} (mx : option A) :
  P → (guard P; mx) = mx.
Proof. intros. by case_option_guard. Qed.
Lemma option_guard_False {A} P `{Decision P} (mx : option A) :
  ¬P → (guard P; mx) = None.
Proof. intros. by case_option_guard. Qed.
Lemma option_guard_iff {A} P Q `{Decision P, Decision Q} (mx : option A) :
  (P ↔ Q) → (guard P; mx) = guard Q; mx.
Proof. intros [??]. repeat case_option_guard; intuition. Qed.

Tactic Notation "simpl_option" "by" tactic3(tac) :=
  let assert_Some_None A mx H := first
    [ let x := fresh in evar (x:A); let x' := eval unfold x in x in clear x;
      assert (mx = Some x') as H by tac
    | assert (mx = None) as H by tac ]
  in repeat match goal with
  | H : context [@mret _ _ ?A] |- _ =>
     change (@mret _ _ A) with (@Some A) in H
  | |- context [@mret _ _ ?A] => change (@mret _ _ A) with (@Some A)
  | H : context [mbind (M:=option) (A:=?A) ?f ?mx] |- _ =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
  | H : context [fmap (M:=option) (A:=?A) ?f ?mx] |- _ =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
  | H : context [from_option (A:=?A) _ _ ?mx] |- _ =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
  | H : context [ match ?mx with _ => _ end ] |- _ =>
    match type of mx with
    | option ?A =>
      let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx in H; clear Hx
    end
  | |- context [mbind (M:=option) (A:=?A) ?f ?mx] =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
  | |- context [fmap (M:=option) (A:=?A) ?f ?mx] =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
  | |- context [from_option (A:=?A) _ _ ?mx] =>
    let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
  | |- context [ match ?mx with _ => _ end ] =>
    match type of mx with
    | option ?A =>
      let Hx := fresh in assert_Some_None A mx Hx; rewrite Hx; clear Hx
    end
  | H : context [decide _] |- _ => rewrite decide_True in H by tac
  | H : context [decide _] |- _ => rewrite decide_False in H by tac
  | H : context [mguard _ _] |- _ => rewrite option_guard_False in H by tac
  | H : context [mguard _ _] |- _ => rewrite option_guard_True in H by tac
  | _ => rewrite decide_True by tac
  | _ => rewrite decide_False by tac
  | _ => rewrite option_guard_True by tac
  | _ => rewrite option_guard_False by tac
  | H : context [None ∪ _] |- _ => rewrite (left_id_L None (∪)) in H
  | H : context [_ ∪ None] |- _ => rewrite (right_id_L None (∪)) in H
  | |- context [None ∪ _] => rewrite (left_id_L None (∪))
  | |- context [_ ∪ None] => rewrite (right_id_L None (∪))
  end.
Tactic Notation "simplify_option_eq" "by" tactic3(tac) :=
  repeat match goal with
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | _ : maybe _ ?x = Some _ |- _ => is_var x; destruct x
  | _ : maybe2 _ ?x = Some _ |- _ => is_var x; destruct x
  | _ : maybe3 _ ?x = Some _ |- _ => is_var x; destruct x
  | _ : maybe4 _ ?x = Some _ |- _ => is_var x; destruct x
  | H : _ ∪ _ = Some _ |- _ => apply option_union_Some in H; destruct H
  | H : mbind (M:=option) ?f ?mx = ?my |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (f x = my) in H|change (None = my) in H]
  | H : ?my = mbind (M:=option) ?f ?mx |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (my = f x) in H|change (my = None) in H]
  | H : fmap (M:=option) ?f ?mx = ?my |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (Some (f x) = my) in H|change (None = my) in H]
  | H : ?my = fmap (M:=option) ?f ?mx |- _ =>
    match mx with Some _ => fail 1 | None => fail 1 | _ => idtac end;
    match my with Some _ => idtac | None => idtac | _ => fail 1 end;
    let x := fresh in destruct mx as [x|] eqn:?;
      [change (my = Some (f x)) in H|change (my = None) in H]
  | _ => progress case_decide
  | _ => progress case_option_guard
  end.
Tactic Notation "simplify_option_eq" := simplify_option_eq by eauto.
