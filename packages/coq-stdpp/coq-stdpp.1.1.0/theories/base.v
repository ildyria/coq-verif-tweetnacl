(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects type class interfaces, notations, and general theorems
that are used throughout the whole development. Most importantly it contains
abstract interfaces for ordered structures, collections, and various other data
structures. *)

From Coq Require Export Morphisms RelationClasses List Bool Utf8 Setoid.
Set Default Proof Using "Type".
Export ListNotations.
From Coq.Program Require Export Basics Syntax.

(** Enable implicit generalization. *)
(* This option enables implicit generalization in arguments of the form
   `{...} (i.e., anonymous arguments).  Unfortunately, it also enables
   implicit generalization in `Instance`.  We think that the fact taht both
   behaviors are coupled together is a [bug in
   Coq](https://github.com/coq/coq/issues/6030). *)
Global Generalizable All Variables.

(** * Tweak program *)
(** 1. Since we only use Program to solve logical side-conditions, they should
always be made Opaque, otherwise we end up with performance problems due to
Coq blindly unfolding them.

Note that in most cases we use [Next Obligation. (* ... *) Qed.], for which
this option does not matter. However, sometimes we write things like
[Solve Obligations with naive_solver (* ... *)], and then the obligations
should surely be opaque. *)
Global Unset Transparent Obligations.

(** 2. Do not let Program automatically simplify obligations. The default
obligation tactic is [Tactics.program_simpl], which, among other things,
introduces all variables and gives them fresh names. As such, it becomes
impossible to refer to hypotheses in a robust way. *)
Obligation Tactic := idtac.

(** 3. Hide obligations from the results of the [Search] commands. *)
Add Search Blacklist "_obligation_".

(** * Sealing off definitions *)
Section seal.
  Local Set Primitive Projections.
  Record seal {A} (f : A) := { unseal : A; seal_eq : unseal = f }.
End seal.
Arguments unseal {_ _} _ : assert.
Arguments seal_eq {_ _} _ : assert.

(** * Typeclass opaque definitions *)
(* The constant [tc_opaque] is used to make definitions opaque for just type
class search. Note that [simpl] is set up to always unfold [tc_opaque]. *)
Definition tc_opaque {A} (x : A) : A := x.
Typeclasses Opaque tc_opaque.
Arguments tc_opaque {_} _ /.

(* Below we define type class versions of the common logical operators. It is
important to note that we duplicate the definitions, and do not declare the
existing logical operators as type classes. That is, we do not say:

  Existing Class or.
  Existing Class and.

If we could define the existing logical operators as classes, there is no way
of disambiguating whether a premise of a lemma should be solved by type class
resolution or not.

These classes are useful for two purposes: writing complicated type class
premises in a more concise way, and for efficiency. For example, using the [Or]
class, instead of defining two instances [P → Q1 → R] and [P → Q2 → R] we could
have one instance [P → Or Q1 Q2 → R]. When we declare the instance that way, we
avoid the need to derive [P] twice. *)
Inductive TCOr (P1 P2 : Prop) : Prop :=
  | TCOr_l : P1 → TCOr P1 P2
  | TCOr_r : P2 → TCOr P1 P2.
Existing Class TCOr.
Existing Instance TCOr_l | 9.
Existing Instance TCOr_r | 10.

Inductive TCAnd (P1 P2 : Prop) : Prop := TCAnd_intro : P1 → P2 → TCAnd P1 P2.
Existing Class TCAnd.
Existing Instance TCAnd_intro.

Inductive TCTrue : Prop := TCTrue_intro : TCTrue.
Existing Class TCTrue.
Existing Instance TCTrue_intro.

Inductive TCForall {A} (P : A → Prop) : list A → Prop :=
  | TCForall_nil : TCForall P []
  | TCForall_cons x xs : P x → TCForall P xs → TCForall P (x :: xs).
Existing Class TCForall.
Existing Instance TCForall_nil.
Existing Instance TCForall_cons.

Inductive TCForall2 {A B} (P : A → B → Prop) : list A → list B → Prop :=
  | TCForall2_nil : TCForall2 P [] []
  | TCForall2_cons x y xs ys :
     P x y → TCForall2 P xs ys → TCForall2 P (x :: xs) (y :: ys).
Existing Class TCForall2.
Existing Instance TCForall2_nil.
Existing Instance TCForall2_cons.

(** Throughout this development we use [stdpp_scope] for all general purpose
notations that do not belong to a more specific scope. *)
Delimit Scope stdpp_scope with stdpp.
Global Open Scope stdpp_scope.

(** Change [True] and [False] into notations in order to enable overloading.
We will use this to give [True] and [False] a different interpretation for
embedded logics. *)
Notation "'True'" := True : type_scope.
Notation "'False'" := False : type_scope.


(** * Equality *)
(** Introduce some Haskell style like notations. *)
Notation "(=)" := eq (only parsing) : stdpp_scope.
Notation "( x =)" := (eq x) (only parsing) : stdpp_scope.
Notation "(= x )" := (λ y, eq y x) (only parsing) : stdpp_scope.
Notation "(≠)" := (λ x y, x ≠ y) (only parsing) : stdpp_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing) : stdpp_scope.
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing) : stdpp_scope.

Hint Extern 0 (_ = _) => reflexivity.
Hint Extern 100 (_ ≠ _) => discriminate.

Instance: @PreOrder A (=).
Proof. split; repeat intro; congruence. Qed.

(** ** Setoid equality *)
(** We define an operational type class for setoid equality, i.e., the
"canonical" equivalence for a type. The typeclass is tied to the \equiv
symbol. This is based on (Spitters/van der Weegen, 2011). *)
Class Equiv A := equiv: relation A.
(* No Hint Mode set because of Coq bug #5735
Hint Mode Equiv ! : typeclass_instances. *)

Infix "≡" := equiv (at level 70, no associativity) : stdpp_scope.
Notation "(≡)" := equiv (only parsing) : stdpp_scope.
Notation "( X ≡)" := (equiv X) (only parsing) : stdpp_scope.
Notation "(≡ X )" := (λ Y, Y ≡ X) (only parsing) : stdpp_scope.
Notation "(≢)" := (λ X Y, ¬X ≡ Y) (only parsing) : stdpp_scope.
Notation "X ≢ Y":= (¬X ≡ Y) (at level 70, no associativity) : stdpp_scope.
Notation "( X ≢)" := (λ Y, X ≢ Y) (only parsing) : stdpp_scope.
Notation "(≢ X )" := (λ Y, Y ≢ X) (only parsing) : stdpp_scope.

(** The type class [LeibnizEquiv] collects setoid equalities that coincide
with Leibniz equality. We provide the tactic [fold_leibniz] to transform such
setoid equalities into Leibniz equalities, and [unfold_leibniz] for the
reverse. *)
Class LeibnizEquiv A `{Equiv A} := leibniz_equiv x y : x ≡ y → x = y.
Hint Mode LeibnizEquiv ! - : typeclass_instances.

Lemma leibniz_equiv_iff `{LeibnizEquiv A, !Reflexive (@equiv A _)} (x y : A) :
  x ≡ y ↔ x = y.
Proof. split. apply leibniz_equiv. intros ->; reflexivity. Qed.

Ltac fold_leibniz := repeat
  match goal with
  | H : context [ @equiv ?A _ _ _ ] |- _ =>
    setoid_rewrite (leibniz_equiv_iff (A:=A)) in H
  | |- context [ @equiv ?A _ _ _ ] =>
    setoid_rewrite (leibniz_equiv_iff (A:=A))
  end.
Ltac unfold_leibniz := repeat
  match goal with
  | H : context [ @eq ?A _ _ ] |- _ =>
    setoid_rewrite <-(leibniz_equiv_iff (A:=A)) in H
  | |- context [ @eq ?A _ _ ] =>
    setoid_rewrite <-(leibniz_equiv_iff (A:=A))
  end.

Definition equivL {A} : Equiv A := (=).

(** A [Params f n] instance forces the setoid rewriting mechanism not to
rewrite in the first [n] arguments of the function [f]. We will declare such
instances for all operational type classes in this development. *)
Instance: Params (@equiv) 2.

(** The following instance forces [setoid_replace] to use setoid equality
(for types that have an [Equiv] instance) rather than the standard Leibniz
equality. *)
Instance equiv_default_relation `{Equiv A} : DefaultRelation (≡) | 3.
Hint Extern 0 (_ ≡ _) => reflexivity.
Hint Extern 0 (_ ≡ _) => symmetry; assumption.


(** * Type classes *)
(** ** Decidable propositions *)
(** This type class by (Spitters/van der Weegen, 2011) collects decidable
propositions. *)
Class Decision (P : Prop) := decide : {P} + {¬P}.
Hint Mode Decision ! : typeclass_instances.
Arguments decide _ {_} : simpl never, assert.

(** Although [RelDecision R] is just [∀ x y, Decision (R x y)], we make this
an explicit class instead of a notation for two reasons:

- It allows us to control [Hint Mode] more precisely. In particular, if it were
  defined as a notation, the above [Hint Mode] for [Decision] would not prevent
  diverging instance search when looking for [RelDecision (@eq ?A)], which would
  result in it looking for [Decision (@eq ?A x y)], i.e. an instance where the
  head position of [Decision] is not en evar.
- We use it to avoid inefficient computation due to eager evaluation of
  propositions by [vm_compute]. This inefficiency arises for example if
  [(x = y) := (f x = f y)]. Since [decide (x = y)] evaluates to
  [decide (f x = f y)], this would then lead to evaluation of [f x] and [f y].
  Using the [RelDecision], the [f] is hidden under a lambda, which prevents
  unnecessary evaluation. *)
Class RelDecision {A B} (R : A → B → Prop) :=
  decide_rel x y :> Decision (R x y).
Hint Mode RelDecision ! ! ! : typeclass_instances.
Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.
Notation EqDecision A := (RelDecision (@eq A)).

(** ** Inhabited types *)
(** This type class collects types that are inhabited. *)
Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Hint Mode Inhabited ! : typeclass_instances.
Arguments populate {_} _ : assert.

(** ** Proof irrelevant types *)
(** This type class collects types that are proof irrelevant. That means, all
elements of the type are equal. We use this notion only used for propositions,
but by universe polymorphism we can generalize it. *)
Class ProofIrrel (A : Type) : Prop := proof_irrel (x y : A) : x = y.
Hint Mode ProofIrrel ! : typeclass_instances.

(** ** Common properties *)
(** These operational type classes allow us to refer to common mathematical
properties in a generic way. For example, for injectivity of [(k ++)] it
allows us to write [inj (k ++)] instead of [app_inv_head k]. *)
Class Inj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop :=
  inj x y : S (f x) (f y) → R x y.
Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A → B → C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) → R1 x1 y1 ∧ R2 x2 y2.
Class Cancel {A B} (S : relation B) (f : A → B) (g : B → A) : Prop :=
  cancel : ∀ x, S (f (g x)) x.
Class Surj {A B} (R : relation B) (f : A → B) :=
  surj y : ∃ x, R (f x) y.
Class IdemP {A} (R : relation A) (f : A → A → A) : Prop :=
  idemp x : R (f x x) x.
Class Comm {A B} (R : relation A) (f : B → B → A) : Prop :=
  comm x y : R (f x y) (f y x).
Class LeftId {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  left_id x : R (f i x) x.
Class RightId {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  right_id x : R (f x i) x.
Class Assoc {A} (R : relation A) (f : A → A → A) : Prop :=
  assoc x y z : R (f x (f y z)) (f (f x y) z).
Class LeftAbsorb {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  left_absorb x : R (f i x) i.
Class RightAbsorb {A} (R : relation A) (i : A) (f : A → A → A) : Prop :=
  right_absorb x : R (f x i) i.
Class AntiSymm {A} (R S : relation A) : Prop :=
  anti_symm x y : S x y → S y x → R x y.
Class Total {A} (R : relation A) := total x y : R x y ∨ R y x.
Class Trichotomy {A} (R : relation A) :=
  trichotomy x y : R x y ∨ x = y ∨ R y x.
Class TrichotomyT {A} (R : relation A) :=
  trichotomyT x y : {R x y} + {x = y} + {R y x}.

Arguments irreflexivity {_} _ {_} _ _ : assert.
Arguments inj {_ _ _ _} _ {_} _ _ _ : assert.
Arguments inj2 {_ _ _ _ _ _} _ {_} _ _ _ _ _: assert.
Arguments cancel {_ _ _} _ _ {_} _ : assert.
Arguments surj {_ _ _} _ {_} _ : assert.
Arguments idemp {_ _} _ {_} _ : assert.
Arguments comm {_ _ _} _ {_} _ _ : assert.
Arguments left_id {_ _} _ _ {_} _ : assert.
Arguments right_id {_ _} _ _ {_} _ : assert.
Arguments assoc {_ _} _ {_} _ _ _ : assert.
Arguments left_absorb {_ _} _ _ {_} _ : assert.
Arguments right_absorb {_ _} _ _ {_} _ : assert.
Arguments anti_symm {_ _} _ {_} _ _ _ _ : assert.
Arguments total {_} _ {_} _ _ : assert.
Arguments trichotomy {_} _ {_} _ _ : assert.
Arguments trichotomyT {_} _ {_} _ _ : assert.

Lemma not_symmetry `{R : relation A, !Symmetric R} x y : ¬R x y → ¬R y x.
Proof. intuition. Qed.
Lemma symmetry_iff `(R : relation A) `{!Symmetric R} x y : R x y ↔ R y x.
Proof. intuition. Qed.

Lemma not_inj `{Inj A B R R' f} x y : ¬R x y → ¬R' (f x) (f y).
Proof. intuition. Qed.
Lemma not_inj2_1 `{Inj2 A B C R R' R'' f} x1 x2 y1 y2 :
  ¬R x1 x2 → ¬R'' (f x1 y1) (f x2 y2).
Proof. intros HR HR''. destruct (inj2 f x1 y1 x2 y2); auto. Qed.
Lemma not_inj2_2 `{Inj2 A B C R R' R'' f} x1 x2 y1 y2 :
  ¬R' y1 y2 → ¬R'' (f x1 y1) (f x2 y2).
Proof. intros HR' HR''. destruct (inj2 f x1 y1 x2 y2); auto. Qed.

Lemma inj_iff {A B} {R : relation A} {S : relation B} (f : A → B)
  `{!Inj R S f} `{!Proper (R ==> S) f} x y : S (f x) (f y) ↔ R x y.
Proof. firstorder. Qed.
Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 f} y : Inj R1 R3 (λ x, f x y).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.
Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 f} x : Inj R2 R3 (f x).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.

Lemma cancel_inj `{Cancel A B R1 f g, !Equivalence R1, !Proper (R2 ==> R1) f} :
  Inj R1 R2 g.
Proof.
  intros x y E. rewrite <-(cancel f g x), <-(cancel f g y), E. reflexivity.
Qed.
Lemma cancel_surj `{Cancel A B R1 f g} : Surj R1 f.
Proof. intros y. exists (g y). auto. Qed.

(** The following lemmas are specific versions of the projections of the above
type classes for Leibniz equality. These lemmas allow us to enforce Coq not to
use the setoid rewriting mechanism. *)
Lemma idemp_L {A} f `{!@IdemP A (=) f} x : f x x = x.
Proof. auto. Qed.
Lemma comm_L {A B} f `{!@Comm A B (=) f} x y : f x y = f y x.
Proof. auto. Qed.
Lemma left_id_L {A} i f `{!@LeftId A (=) i f} x : f i x = x.
Proof. auto. Qed.
Lemma right_id_L {A} i f `{!@RightId A (=) i f} x : f x i = x.
Proof. auto. Qed.
Lemma assoc_L {A} f `{!@Assoc A (=) f} x y z : f x (f y z) = f (f x y) z.
Proof. auto. Qed.
Lemma left_absorb_L {A} i f `{!@LeftAbsorb A (=) i f} x : f i x = i.
Proof. auto. Qed.
Lemma right_absorb_L {A} i f `{!@RightAbsorb A (=) i f} x : f x i = i.
Proof. auto. Qed.

(** ** Generic orders *)
(** The classes [PreOrder], [PartialOrder], and [TotalOrder] use an arbitrary
relation [R] instead of [⊆] to support multiple orders on the same type. *)
Definition strict {A} (R : relation A) : relation A := λ X Y, R X Y ∧ ¬R Y X.
Instance: Params (@strict) 2.
Class PartialOrder {A} (R : relation A) : Prop := {
  partial_order_pre :> PreOrder R;
  partial_order_anti_symm :> AntiSymm (=) R
}.
Class TotalOrder {A} (R : relation A) : Prop := {
  total_order_partial :> PartialOrder R;
  total_order_trichotomy :> Trichotomy (strict R)
}.

(** * Logic *)
Notation "(∧)" := and (only parsing) : stdpp_scope.
Notation "( A ∧)" := (and A) (only parsing) : stdpp_scope.
Notation "(∧ B )" := (λ A, A ∧ B) (only parsing) : stdpp_scope.

Notation "(∨)" := or (only parsing) : stdpp_scope.
Notation "( A ∨)" := (or A) (only parsing) : stdpp_scope.
Notation "(∨ B )" := (λ A, A ∨ B) (only parsing) : stdpp_scope.

Notation "(↔)" := iff (only parsing) : stdpp_scope.
Notation "( A ↔)" := (iff A) (only parsing) : stdpp_scope.
Notation "(↔ B )" := (λ A, A ↔ B) (only parsing) : stdpp_scope.

Hint Extern 0 (_ ↔ _) => reflexivity.
Hint Extern 0 (_ ↔ _) => symmetry; assumption.

Lemma or_l P Q : ¬Q → P ∨ Q ↔ P.
Proof. tauto. Qed.
Lemma or_r P Q : ¬P → P ∨ Q ↔ Q.
Proof. tauto. Qed.
Lemma and_wlog_l (P Q : Prop) : (Q → P) → Q → (P ∧ Q).
Proof. tauto. Qed.
Lemma and_wlog_r (P Q : Prop) : P → (P → Q) → (P ∧ Q).
Proof. tauto. Qed.
Lemma impl_transitive (P Q R : Prop) : (P → Q) → (Q → R) → (P → R).
Proof. tauto. Qed.
Lemma forall_proper {A} (P Q : A → Prop) :
  (∀ x, P x ↔ Q x) → (∀ x, P x) ↔ (∀ x, Q x).
Proof. firstorder. Qed.
Lemma exist_proper {A} (P Q : A → Prop) :
  (∀ x, P x ↔ Q x) → (∃ x, P x) ↔ (∃ x, Q x).
Proof. firstorder. Qed.

Instance: Comm (↔) (@eq A).
Proof. red; intuition. Qed.
Instance: Comm (↔) (λ x y, @eq A y x).
Proof. red; intuition. Qed.
Instance: Comm (↔) (↔).
Proof. red; intuition. Qed.
Instance: Comm (↔) (∧).
Proof. red; intuition. Qed.
Instance: Assoc (↔) (∧).
Proof. red; intuition. Qed.
Instance: IdemP (↔) (∧).
Proof. red; intuition. Qed.
Instance: Comm (↔) (∨).
Proof. red; intuition. Qed.
Instance: Assoc (↔) (∨).
Proof. red; intuition. Qed.
Instance: IdemP (↔) (∨).
Proof. red; intuition. Qed.
Instance: LeftId (↔) True (∧).
Proof. red; intuition. Qed.
Instance: RightId (↔) True (∧).
Proof. red; intuition. Qed.
Instance: LeftAbsorb (↔) False (∧).
Proof. red; intuition. Qed.
Instance: RightAbsorb (↔) False (∧).
Proof. red; intuition. Qed.
Instance: LeftId (↔) False (∨).
Proof. red; intuition. Qed.
Instance: RightId (↔) False (∨).
Proof. red; intuition. Qed.
Instance: LeftAbsorb (↔) True (∨).
Proof. red; intuition. Qed.
Instance: RightAbsorb (↔) True (∨).
Proof. red; intuition. Qed.
Instance: LeftId (↔) True impl.
Proof. unfold impl. red; intuition. Qed.
Instance: RightAbsorb (↔) True impl.
Proof. unfold impl. red; intuition. Qed.


(** * Common data types *)
(** ** Functions *)
Notation "(→)" := (λ A B, A → B) (only parsing) : stdpp_scope.
Notation "( A →)" := (λ B, A → B) (only parsing) : stdpp_scope.
Notation "(→ B )" := (λ A, A → B) (only parsing) : stdpp_scope.

Notation "t $ r" := (t r)
  (at level 65, right associativity, only parsing) : stdpp_scope.
Notation "($)" := (λ f x, f x) (only parsing) : stdpp_scope.
Notation "($ x )" := (λ f, f x) (only parsing) : stdpp_scope.

Infix "∘" := compose : stdpp_scope.
Notation "(∘)" := compose (only parsing) : stdpp_scope.
Notation "( f ∘)" := (compose f) (only parsing) : stdpp_scope.
Notation "(∘ f )" := (λ g, compose g f) (only parsing) : stdpp_scope.

Instance impl_inhabited {A} `{Inhabited B} : Inhabited (A → B) :=
  populate (λ _, inhabitant).

(** Ensure that [simpl] unfolds [id], [compose], and [flip] when fully
applied. *)
Arguments id _ _ / : assert.
Arguments compose _ _ _ _ _ _ / : assert.
Arguments flip _ _ _ _ _ _ / : assert.
Arguments const _ _ _ _ / : assert.
Typeclasses Transparent id compose flip const.

Definition fun_map {A A' B B'} (f: A' → A) (g: B → B') (h : A → B) : A' → B' :=
  g ∘ h ∘ f.

Instance const_proper `{R1 : relation A, R2 : relation B} (x : B) :
  Reflexive R2 → Proper (R1 ==> R2) (λ _, x).
Proof. intros ? y1 y2; reflexivity. Qed.

Instance id_inj {A} : Inj (=) (=) (@id A).
Proof. intros ??; auto. Qed.
Instance compose_inj {A B C} R1 R2 R3 (f : A → B) (g : B → C) :
  Inj R1 R2 f → Inj R2 R3 g → Inj R1 R3 (g ∘ f).
Proof. red; intuition. Qed.

Instance id_surj {A} : Surj (=) (@id A).
Proof. intros y; exists y; reflexivity. Qed.
Instance compose_surj {A B C} R (f : A → B) (g : B → C) :
  Surj (=) f → Surj R g → Surj R (g ∘ f).
Proof.
  intros ?? x. unfold compose. destruct (surj g x) as [y ?].
  destruct (surj f y) as [z ?]. exists z. congruence.
Qed.

Instance id_comm {A B} (x : B) : Comm (=) (λ _ _ : A, x).
Proof. intros ?; reflexivity. Qed.
Instance id_assoc {A} (x : A) : Assoc (=) (λ _ _ : A, x).
Proof. intros ???; reflexivity. Qed.
Instance const1_assoc {A} : Assoc (=) (λ x _ : A, x).
Proof. intros ???; reflexivity. Qed.
Instance const2_assoc {A} : Assoc (=) (λ _ x : A, x).
Proof. intros ???; reflexivity. Qed.
Instance const1_idemp {A} : IdemP (=) (λ x _ : A, x).
Proof. intros ?; reflexivity. Qed.
Instance const2_idemp {A} : IdemP (=) (λ _ x : A, x).
Proof. intros ?; reflexivity. Qed.

(** ** Lists *)
Instance list_inhabited {A} : Inhabited (list A) := populate [].

Definition zip_with {A B C} (f : A → B → C) : list A → list B → list C :=
  fix go l1 l2 :=
  match l1, l2 with x1 :: l1, x2 :: l2 => f x1 x2 :: go l1 l2 | _ , _ => [] end.
Notation zip := (zip_with pair).

(** ** Booleans *)
(** The following coercion allows us to use Booleans as propositions. *)
Coercion Is_true : bool >-> Sortclass.
Hint Unfold Is_true.
Hint Immediate Is_true_eq_left.
Hint Resolve orb_prop_intro andb_prop_intro.
Notation "(&&)" := andb (only parsing).
Notation "(||)" := orb (only parsing).
Infix "&&*" := (zip_with (&&)) (at level 40).
Infix "||*" := (zip_with (||)) (at level 50).

Instance bool_inhabated : Inhabited bool := populate true.

Definition bool_le (β1 β2 : bool) : Prop := negb β1 || β2.
Infix "=.>" := bool_le (at level 70).
Infix "=.>*" := (Forall2 bool_le) (at level 70).
Instance: PartialOrder bool_le.
Proof. repeat split; repeat intros [|]; compute; tauto. Qed.

Lemma andb_True b1 b2 : b1 && b2 ↔ b1 ∧ b2.
Proof. destruct b1, b2; simpl; tauto. Qed.
Lemma orb_True b1 b2 : b1 || b2 ↔ b1 ∨ b2.
Proof. destruct b1, b2; simpl; tauto. Qed.
Lemma negb_True b : negb b ↔ ¬b.
Proof. destruct b; simpl; tauto. Qed.
Lemma Is_true_false (b : bool) : b = false → ¬b.
Proof. now intros -> ?. Qed.

(** ** Unit *)
Instance unit_equiv : Equiv unit := λ _ _, True.
Instance unit_equivalence : Equivalence (@equiv unit _).
Proof. repeat split. Qed.
Instance unit_leibniz : LeibnizEquiv unit.
Proof. intros [] []; reflexivity. Qed.
Instance unit_inhabited: Inhabited unit := populate ().

(** ** Products *)
Notation "( x ,)" := (pair x) (only parsing) : stdpp_scope.
Notation "(, y )" := (λ x, (x,y)) (only parsing) : stdpp_scope.

Notation "p .1" := (fst p) (at level 2, left associativity, format "p .1").
Notation "p .2" := (snd p) (at level 2, left associativity, format "p .2").

Instance: Params (@pair) 2.
Instance: Params (@fst) 2.
Instance: Params (@snd) 2.

Notation curry := prod_curry.
Notation uncurry := prod_uncurry.
Definition curry3 {A B C D} (f : A → B → C → D) (p : A * B * C) : D :=
  let '(a,b,c) := p in f a b c.
Definition curry4 {A B C D E} (f : A → B → C → D → E) (p : A * B * C * D) : E :=
  let '(a,b,c,d) := p in f a b c d.

Definition uncurry3 {A B C D} (f : A * B * C → D) (a : A) (b : B) (c : C) : D :=
  f (a, b, c).
Definition uncurry4 {A B C D E} (f : A * B * C * D → E)
  (a : A) (b : B) (c : C) (d : D) : E := f (a, b, c, d).

Definition prod_map {A A' B B'} (f: A → A') (g: B → B') (p : A * B) : A' * B' :=
  (f (p.1), g (p.2)).
Arguments prod_map {_ _ _ _} _ _ !_ / : assert.

Definition prod_zip {A A' A'' B B' B''} (f : A → A' → A'') (g : B → B' → B'')
    (p : A * B) (q : A' * B') : A'' * B'' := (f (p.1) (q.1), g (p.2) (q.2)).
Arguments prod_zip {_ _ _ _ _ _} _ _ !_ !_ / : assert.

Instance prod_inhabited {A B} (iA : Inhabited A)
    (iB : Inhabited B) : Inhabited (A * B) :=
  match iA, iB with populate x, populate y => populate (x,y) end.

Instance pair_inj : Inj2 (=) (=) (=) (@pair A B).
Proof. injection 1; auto. Qed.
Instance prod_map_inj {A A' B B'} (f : A → A') (g : B → B') :
  Inj (=) (=) f → Inj (=) (=) g → Inj (=) (=) (prod_map f g).
Proof.
  intros ?? [??] [??] ?; simpl in *; f_equal;
    [apply (inj f)|apply (inj g)]; congruence.
Qed.

Definition prod_relation {A B} (R1 : relation A) (R2 : relation B) :
  relation (A * B) := λ x y, R1 (x.1) (y.1) ∧ R2 (x.2) (y.2).
Section prod_relation.
  Context `{R1 : relation A, R2 : relation B}.
  Global Instance prod_relation_refl :
    Reflexive R1 → Reflexive R2 → Reflexive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_sym :
    Symmetric R1 → Symmetric R2 → Symmetric (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_trans :
    Transitive R1 → Transitive R2 → Transitive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_equiv :
    Equivalence R1 → Equivalence R2 → Equivalence (prod_relation R1 R2).
  Proof. split; apply _. Qed.

  Global Instance pair_proper' : Proper (R1 ==> R2 ==> prod_relation R1 R2) pair.
  Proof. firstorder eauto. Qed.
  Global Instance pair_inj' : Inj2 R1 R2 (prod_relation R1 R2) pair.
  Proof. inversion_clear 1; eauto. Qed.
  Global Instance fst_proper' : Proper (prod_relation R1 R2 ==> R1) fst.
  Proof. firstorder eauto. Qed.
  Global Instance snd_proper' : Proper (prod_relation R1 R2 ==> R2) snd.
  Proof. firstorder eauto. Qed.
End prod_relation.

Instance prod_equiv `{Equiv A,Equiv B} : Equiv (A * B) := prod_relation (≡) (≡).
Instance pair_proper `{Equiv A, Equiv B} :
  Proper ((≡) ==> (≡) ==> (≡)) (@pair A B) := _.
Instance pair_equiv_inj `{Equiv A, Equiv B} : Inj2 (≡) (≡) (≡) (@pair A B) := _.
Instance fst_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@fst A B) := _.
Instance snd_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@snd A B) := _.
Typeclasses Opaque prod_equiv.

Instance prod_leibniz `{LeibnizEquiv A, LeibnizEquiv B} : LeibnizEquiv (A * B).
Proof. intros [??] [??] [??]; f_equal; apply leibniz_equiv; auto. Qed.

(** ** Sums *)
Definition sum_map {A A' B B'} (f: A → A') (g: B → B') (xy : A + B) : A' + B' :=
  match xy with inl x => inl (f x) | inr y => inr (g y) end.
Arguments sum_map {_ _ _ _} _ _ !_ / : assert.

Instance sum_inhabited_l {A B} (iA : Inhabited A) : Inhabited (A + B) :=
  match iA with populate x => populate (inl x) end.
Instance sum_inhabited_r {A B} (iB : Inhabited A) : Inhabited (A + B) :=
  match iB with populate y => populate (inl y) end.

Instance inl_inj : Inj (=) (=) (@inl A B).
Proof. injection 1; auto. Qed.
Instance inr_inj : Inj (=) (=) (@inr A B).
Proof. injection 1; auto. Qed.

Instance sum_map_inj {A A' B B'} (f : A → A') (g : B → B') :
  Inj (=) (=) f → Inj (=) (=) g → Inj (=) (=) (sum_map f g).
Proof. intros ?? [?|?] [?|?] [=]; f_equal; apply (inj _); auto. Qed.

Inductive sum_relation {A B}
     (R1 : relation A) (R2 : relation B) : relation (A + B) :=
  | inl_related x1 x2 : R1 x1 x2 → sum_relation R1 R2 (inl x1) (inl x2)
  | inr_related y1 y2 : R2 y1 y2 → sum_relation R1 R2 (inr y1) (inr y2).

Section sum_relation.
  Context `{R1 : relation A, R2 : relation B}.
  Global Instance sum_relation_refl :
    Reflexive R1 → Reflexive R2 → Reflexive (sum_relation R1 R2).
  Proof. intros ?? [?|?]; constructor; reflexivity. Qed.
  Global Instance sum_relation_sym :
    Symmetric R1 → Symmetric R2 → Symmetric (sum_relation R1 R2).
  Proof. destruct 3; constructor; eauto. Qed.
  Global Instance sum_relation_trans :
    Transitive R1 → Transitive R2 → Transitive (sum_relation R1 R2).
  Proof. destruct 3; inversion_clear 1; constructor; eauto. Qed.
  Global Instance sum_relation_equiv :
    Equivalence R1 → Equivalence R2 → Equivalence (sum_relation R1 R2).
  Proof. split; apply _. Qed.
  Global Instance inl_proper' : Proper (R1 ==> sum_relation R1 R2) inl.
  Proof. constructor; auto. Qed.
  Global Instance inr_proper' : Proper (R2 ==> sum_relation R1 R2) inr.
  Proof. constructor; auto. Qed.
  Global Instance inl_inj' : Inj R1 (sum_relation R1 R2) inl.
  Proof. inversion_clear 1; auto. Qed.
  Global Instance inr_inj' : Inj R2 (sum_relation R1 R2) inr.
  Proof. inversion_clear 1; auto. Qed.
End sum_relation.

Instance sum_equiv `{Equiv A, Equiv B} : Equiv (A + B) := sum_relation (≡) (≡).
Instance inl_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@inl A B) := _.
Instance inr_proper `{Equiv A, Equiv B} : Proper ((≡) ==> (≡)) (@inr A B) := _.
Instance inl_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inl A B) := _.
Instance inr_equiv_inj `{Equiv A, Equiv B} : Inj (≡) (≡) (@inr A B) := _.
Typeclasses Opaque sum_equiv.

(** ** Option *)
Instance option_inhabited {A} : Inhabited (option A) := populate None.

(** ** Sigma types *)
Arguments existT {_ _} _ _ : assert.
Arguments projT1 {_ _} _ : assert.
Arguments projT2 {_ _} _ : assert.

Arguments exist {_} _ _ _ : assert.
Arguments proj1_sig {_ _} _ : assert.
Arguments proj2_sig {_ _} _ : assert.
Notation "x ↾ p" := (exist _ x p) (at level 20) : stdpp_scope.
Notation "` x" := (proj1_sig x) (at level 10, format "` x") : stdpp_scope.

Lemma proj1_sig_inj {A} (P : A → Prop) x (Px : P x) y (Py : P y) :
  x↾Px = y↾Py → x = y.
Proof. injection 1; trivial. Qed.

Section sig_map.
  Context `{P : A → Prop} `{Q : B → Prop} (f : A → B) (Hf : ∀ x, P x → Q (f x)).
  Definition sig_map (x : sig P) : sig Q := f (`x) ↾ Hf _ (proj2_sig x).
  Global Instance sig_map_inj:
    (∀ x, ProofIrrel (P x)) → Inj (=) (=) f → Inj (=) (=) sig_map.
  Proof.
    intros ?? [x Hx] [y Hy]. injection 1. intros Hxy.
    apply (inj f) in Hxy; subst. rewrite (proof_irrel _ Hy). auto.
  Qed.
End sig_map.
Arguments sig_map _ _ _ _ _ _ !_ / : assert.


(** * Operations on collections *)
(** We define operational type classes for the traditional operations and
relations on collections: the empty collection [∅], the union [(∪)],
intersection [(∩)], and difference [(∖)], the singleton [{[_]}], the subset
[(⊆)] and element of [(∈)] relation, and disjointess [(##)]. *)
Class Empty A := empty: A.
Hint Mode Empty ! : typeclass_instances.
Notation "∅" := empty : stdpp_scope.

Instance empty_inhabited `(Empty A) : Inhabited A := populate ∅.

Class Union A := union: A → A → A.
Hint Mode Union ! : typeclass_instances.
Instance: Params (@union) 2.
Infix "∪" := union (at level 50, left associativity) : stdpp_scope.
Notation "(∪)" := union (only parsing) : stdpp_scope.
Notation "( x ∪)" := (union x) (only parsing) : stdpp_scope.
Notation "(∪ x )" := (λ y, union y x) (only parsing) : stdpp_scope.
Infix "∪*" := (zip_with (∪)) (at level 50, left associativity) : stdpp_scope.
Notation "(∪*)" := (zip_with (∪)) (only parsing) : stdpp_scope.
Infix "∪**" := (zip_with (zip_with (∪)))
  (at level 50, left associativity) : stdpp_scope.
Infix "∪*∪**" := (zip_with (prod_zip (∪) (∪*)))
  (at level 50, left associativity) : stdpp_scope.

Definition union_list `{Empty A} `{Union A} : list A → A := fold_right (∪) ∅.
Arguments union_list _ _ _ !_ / : assert.
Notation "⋃ l" := (union_list l) (at level 20, format "⋃  l") : stdpp_scope.

Class Intersection A := intersection: A → A → A.
Hint Mode Intersection ! : typeclass_instances.
Instance: Params (@intersection) 2.
Infix "∩" := intersection (at level 40) : stdpp_scope.
Notation "(∩)" := intersection (only parsing) : stdpp_scope.
Notation "( x ∩)" := (intersection x) (only parsing) : stdpp_scope.
Notation "(∩ x )" := (λ y, intersection y x) (only parsing) : stdpp_scope.

Class Difference A := difference: A → A → A.
Hint Mode Difference ! : typeclass_instances.
Instance: Params (@difference) 2.
Infix "∖" := difference (at level 40, left associativity) : stdpp_scope.
Notation "(∖)" := difference (only parsing) : stdpp_scope.
Notation "( x ∖)" := (difference x) (only parsing) : stdpp_scope.
Notation "(∖ x )" := (λ y, difference y x) (only parsing) : stdpp_scope.
Infix "∖*" := (zip_with (∖)) (at level 40, left associativity) : stdpp_scope.
Notation "(∖*)" := (zip_with (∖)) (only parsing) : stdpp_scope.
Infix "∖**" := (zip_with (zip_with (∖)))
  (at level 40, left associativity) : stdpp_scope.
Infix "∖*∖**" := (zip_with (prod_zip (∖) (∖*)))
  (at level 50, left associativity) : stdpp_scope.

Class Singleton A B := singleton: A → B.
Hint Mode Singleton - ! : typeclass_instances.
Instance: Params (@singleton) 3.
Notation "{[ x ]}" := (singleton x) (at level 1) : stdpp_scope.
Notation "{[ x ; y ; .. ; z ]}" :=
  (union .. (union (singleton x) (singleton y)) .. (singleton z))
  (at level 1) : stdpp_scope.
Notation "{[ x , y ]}" := (singleton (x,y))
  (at level 1, y at next level) : stdpp_scope.
Notation "{[ x , y , z ]}" := (singleton (x,y,z))
  (at level 1, y at next level, z at next level) : stdpp_scope.

Class SubsetEq A := subseteq: relation A.
Hint Mode SubsetEq ! : typeclass_instances.
Instance: Params (@subseteq) 2.
Infix "⊆" := subseteq (at level 70) : stdpp_scope.
Notation "(⊆)" := subseteq (only parsing) : stdpp_scope.
Notation "( X ⊆)" := (subseteq X) (only parsing) : stdpp_scope.
Notation "(⊆ X )" := (λ Y, Y ⊆ X) (only parsing) : stdpp_scope.
Notation "X ⊈ Y" := (¬X ⊆ Y) (at level 70) : stdpp_scope.
Notation "(⊈)" := (λ X Y, X ⊈ Y) (only parsing) : stdpp_scope.
Notation "( X ⊈)" := (λ Y, X ⊈ Y) (only parsing) : stdpp_scope.
Notation "(⊈ X )" := (λ Y, Y ⊈ X) (only parsing) : stdpp_scope.
Infix "⊆*" := (Forall2 (⊆)) (at level 70) : stdpp_scope.
Notation "(⊆*)" := (Forall2 (⊆)) (only parsing) : stdpp_scope.
Infix "⊆**" := (Forall2 (⊆*)) (at level 70) : stdpp_scope.
Infix "⊆1*" := (Forall2 (λ p q, p.1 ⊆ q.1)) (at level 70) : stdpp_scope.
Infix "⊆2*" := (Forall2 (λ p q, p.2 ⊆ q.2)) (at level 70) : stdpp_scope.
Infix "⊆1**" := (Forall2 (λ p q, p.1 ⊆* q.1)) (at level 70) : stdpp_scope.
Infix "⊆2**" := (Forall2 (λ p q, p.2 ⊆* q.2)) (at level 70) : stdpp_scope.

Hint Extern 0 (_ ⊆ _) => reflexivity.
Hint Extern 0 (_ ⊆* _) => reflexivity.
Hint Extern 0 (_ ⊆** _) => reflexivity.

Infix "⊂" := (strict (⊆)) (at level 70) : stdpp_scope.
Notation "(⊂)" := (strict (⊆)) (only parsing) : stdpp_scope.
Notation "( X ⊂)" := (strict (⊆) X) (only parsing) : stdpp_scope.
Notation "(⊂ X )" := (λ Y, Y ⊂ X) (only parsing) : stdpp_scope.
Notation "X ⊄ Y" := (¬X ⊂ Y) (at level 70) : stdpp_scope.
Notation "(⊄)" := (λ X Y, X ⊄ Y) (only parsing) : stdpp_scope.
Notation "( X ⊄)" := (λ Y, X ⊄ Y) (only parsing) : stdpp_scope.
Notation "(⊄ X )" := (λ Y, Y ⊄ X) (only parsing) : stdpp_scope.

Notation "X ⊆ Y ⊆ Z" := (X ⊆ Y ∧ Y ⊆ Z) (at level 70, Y at next level) : stdpp_scope.
Notation "X ⊆ Y ⊂ Z" := (X ⊆ Y ∧ Y ⊂ Z) (at level 70, Y at next level) : stdpp_scope.
Notation "X ⊂ Y ⊆ Z" := (X ⊂ Y ∧ Y ⊆ Z) (at level 70, Y at next level) : stdpp_scope.
Notation "X ⊂ Y ⊂ Z" := (X ⊂ Y ∧ Y ⊂ Z) (at level 70, Y at next level) : stdpp_scope.

(** The class [Lexico A] is used for the lexicographic order on [A]. This order
is used to create finite maps, finite sets, etc, and is typically different from
the order [(⊆)]. *)
Class Lexico A := lexico: relation A.
Hint Mode Lexico ! : typeclass_instances.

Class ElemOf A B := elem_of: A → B → Prop.
Hint Mode ElemOf - ! : typeclass_instances.
Instance: Params (@elem_of) 3.
Infix "∈" := elem_of (at level 70) : stdpp_scope.
Notation "(∈)" := elem_of (only parsing) : stdpp_scope.
Notation "( x ∈)" := (elem_of x) (only parsing) : stdpp_scope.
Notation "(∈ X )" := (λ x, elem_of x X) (only parsing) : stdpp_scope.
Notation "x ∉ X" := (¬x ∈ X) (at level 80) : stdpp_scope.
Notation "(∉)" := (λ x X, x ∉ X) (only parsing) : stdpp_scope.
Notation "( x ∉)" := (λ X, x ∉ X) (only parsing) : stdpp_scope.
Notation "(∉ X )" := (λ x, x ∉ X) (only parsing) : stdpp_scope.

Class Disjoint A := disjoint : A → A → Prop.
 Hint Mode Disjoint ! : typeclass_instances.
Instance: Params (@disjoint) 2.
Infix "##" := disjoint (at level 70) : stdpp_scope.
Notation "(##)" := disjoint (only parsing) : stdpp_scope.
Notation "( X ##.)" := (disjoint X) (only parsing) : stdpp_scope.
Notation "(.## X )" := (λ Y, Y ## X) (only parsing) : stdpp_scope.
Infix "##*" := (Forall2 (##)) (at level 70) : stdpp_scope.
Notation "(##*)" := (Forall2 (##)) (only parsing) : stdpp_scope.
Infix "##**" := (Forall2 (##*)) (at level 70) : stdpp_scope.
Infix "##1*" := (Forall2 (λ p q, p.1 ## q.1)) (at level 70) : stdpp_scope.
Infix "##2*" := (Forall2 (λ p q, p.2 ## q.2)) (at level 70) : stdpp_scope.
Infix "##1**" := (Forall2 (λ p q, p.1 ##* q.1)) (at level 70) : stdpp_scope.
Infix "##2**" := (Forall2 (λ p q, p.2 ##* q.2)) (at level 70) : stdpp_scope.
Hint Extern 0 (_ ## _) => symmetry; eassumption.
Hint Extern 0 (_ ##* _) => symmetry; eassumption.

Class DisjointE E A := disjointE : E → A → A → Prop.
Hint Mode DisjointE - ! : typeclass_instances.
Instance: Params (@disjointE) 4.
Notation "X ##{ Γ } Y" := (disjointE Γ X Y)
  (at level 70, format "X  ##{ Γ }  Y") : stdpp_scope.
Notation "(##{ Γ } )" := (disjointE Γ) (only parsing, Γ at level 1) : stdpp_scope.
Notation "Xs ##{ Γ }* Ys" := (Forall2 (##{Γ}) Xs Ys)
  (at level 70, format "Xs  ##{ Γ }*  Ys") : stdpp_scope.
Notation "(##{ Γ }* )" := (Forall2 (##{Γ}))
  (only parsing, Γ at level 1) : stdpp_scope.
Notation "X ##{ Γ1 , Γ2 , .. , Γ3 } Y" := (disjoint (pair .. (Γ1, Γ2) .. Γ3) X Y)
  (at level 70, format "X  ##{ Γ1 , Γ2 , .. , Γ3 }  Y") : stdpp_scope.
Notation "Xs ##{ Γ1 , Γ2 , .. , Γ3 }* Ys" :=
  (Forall2 (disjoint (pair .. (Γ1, Γ2) .. Γ3)) Xs Ys)
  (at level 70, format "Xs  ##{ Γ1 ,  Γ2 , .. , Γ3 }*  Ys") : stdpp_scope.
Hint Extern 0 (_ ##{_} _) => symmetry; eassumption.

Class DisjointList A := disjoint_list : list A → Prop.
Hint Mode DisjointList ! : typeclass_instances.
Instance: Params (@disjoint_list) 2.
Notation "## Xs" := (disjoint_list Xs) (at level 20, format "##  Xs") : stdpp_scope.

Section disjoint_list.
  Context `{Disjoint A, Union A, Empty A}.
  Implicit Types X : A.

  Inductive disjoint_list_default : DisjointList A :=
    | disjoint_nil_2 : ## (@nil A)
    | disjoint_cons_2 (X : A) (Xs : list A) : X ## ⋃ Xs → ## Xs → ## (X :: Xs).
  Global Existing Instance disjoint_list_default.

  Lemma disjoint_list_nil  : ## @nil A ↔ True.
  Proof. split; constructor. Qed.
  Lemma disjoint_list_cons X Xs : ## (X :: Xs) ↔ X ## ⋃ Xs ∧ ## Xs.
  Proof. split. inversion_clear 1; auto. intros [??]. constructor; auto. Qed.
End disjoint_list.

Class Filter A B := filter: ∀ (P : A → Prop) `{∀ x, Decision (P x)}, B → B.
Hint Mode Filter - ! : typeclass_instances.

Class UpClose A B := up_close : A → B.
Hint Mode UpClose - ! : typeclass_instances.
Notation "↑ x" := (up_close x) (at level 20, format "↑ x").

(** * Monadic operations *)
(** We define operational type classes for the monadic operations bind, join 
and fmap. We use these type classes merely for convenient overloading of
notations and do not formalize any theory on monads (we do not even define a
class with the monad laws). *)
Class MRet (M : Type → Type) := mret: ∀ {A}, A → M A.
Arguments mret {_ _ _} _ : assert.
Instance: Params (@mret) 3.
Class MBind (M : Type → Type) := mbind : ∀ {A B}, (A → M B) → M A → M B.
Arguments mbind {_ _ _ _} _ !_ / : assert.
Instance: Params (@mbind) 4.
Class MJoin (M : Type → Type) := mjoin: ∀ {A}, M (M A) → M A.
Arguments mjoin {_ _ _} !_ / : assert.
Instance: Params (@mjoin) 3.
Class FMap (M : Type → Type) := fmap : ∀ {A B}, (A → B) → M A → M B.
Arguments fmap {_ _ _ _} _ !_ / : assert.
Instance: Params (@fmap) 4.
Class OMap (M : Type → Type) := omap: ∀ {A B}, (A → option B) → M A → M B.
Arguments omap {_ _ _ _} _ !_ / : assert.
Instance: Params (@omap) 4.

Notation "m ≫= f" := (mbind f m) (at level 60, right associativity) : stdpp_scope.
Notation "( m ≫=)" := (λ f, mbind f m) (only parsing) : stdpp_scope.
Notation "(≫= f )" := (mbind f) (only parsing) : stdpp_scope.
Notation "(≫=)" := (λ m f, mbind f m) (only parsing) : stdpp_scope.

Notation "x ← y ; z" := (y ≫= (λ x : _, z))
  (at level 20, y at level 100, z at level 200, only parsing) : stdpp_scope.

Notation "' x1 .. xn ← y ; z" := (y ≫= (λ x1, .. (λ xn, z) .. ))
  (at level 20, x1 binder, xn binder, y at level 100, z at level 200,
   only parsing, right associativity) : stdpp_scope.

Infix "<$>" := fmap (at level 61, left associativity) : stdpp_scope.

Notation "x ;; z" := (x ≫= λ _, z)
  (at level 100, z at level 200, only parsing, right associativity): stdpp_scope.

Notation "ps .*1" := (fmap (M:=list) fst ps)
  (at level 2, left associativity, format "ps .*1").
Notation "ps .*2" := (fmap (M:=list) snd ps)
  (at level 2, left associativity, format "ps .*2").

Class MGuard (M : Type → Type) :=
  mguard: ∀ P {dec : Decision P} {A}, (P → M A) → M A.
Arguments mguard _ _ _ !_ _ _ / : assert.
Notation "'guard' P ; z" := (mguard P (λ _, z))
  (at level 20, z at level 200, only parsing, right associativity) : stdpp_scope.
Notation "'guard' P 'as' H ; z" := (mguard P (λ H, z))
  (at level 20, z at level 200, only parsing, right associativity) : stdpp_scope.

(** * Operations on maps *)
(** In this section we define operational type classes for the operations
on maps. In the file [fin_maps] we will axiomatize finite maps.
The function look up [m !! k] should yield the element at key [k] in [m]. *)
Class Lookup (K A M : Type) := lookup: K → M → option A.
Hint Mode Lookup - - ! : typeclass_instances.
Instance: Params (@lookup) 4.
Notation "m !! i" := (lookup i m) (at level 20) : stdpp_scope.
Notation "(!!)" := lookup (only parsing) : stdpp_scope.
Notation "( m !!)" := (λ i, m !! i) (only parsing) : stdpp_scope.
Notation "(!! i )" := (lookup i) (only parsing) : stdpp_scope.
Arguments lookup _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The singleton map *)
Class SingletonM K A M := singletonM: K → A → M.
Hint Mode SingletonM - - ! : typeclass_instances.
Instance: Params (@singletonM) 5.
Notation "{[ k := a ]}" := (singletonM k a) (at level 1) : stdpp_scope.

(** The function insert [<[k:=a]>m] should update the element at key [k] with
value [a] in [m]. *)
Class Insert (K A M : Type) := insert: K → A → M → M.
Hint Mode Insert - - ! : typeclass_instances.
Instance: Params (@insert) 5.
Notation "<[ k := a ]>" := (insert k a)
  (at level 5, right associativity, format "<[ k := a ]>") : stdpp_scope.
Arguments insert _ _ _ _ !_ _ !_ / : simpl nomatch, assert.

(** The function delete [delete k m] should delete the value at key [k] in
[m]. If the key [k] is not a member of [m], the original map should be
returned. *)
Class Delete (K M : Type) := delete: K → M → M.
Hint Mode Delete - ! : typeclass_instances.
Instance: Params (@delete) 4.
Arguments delete _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [alter f k m] should update the value at key [k] using the
function [f], which is called with the original value. *)
Class Alter (K A M : Type) := alter: (A → A) → K → M → M.
Hint Mode Alter - - ! : typeclass_instances.
Instance: Params (@alter) 5.
Arguments alter {_ _ _ _} _ !_ !_ / : simpl nomatch, assert.

(** The function [partial_alter f k m] should update the value at key [k] using the
function [f], which is called with the original value at key [k] or [None]
if [k] is not a member of [m]. The value at [k] should be deleted if [f] 
yields [None]. *)
Class PartialAlter (K A M : Type) :=
  partial_alter: (option A → option A) → K → M → M.
Hint Mode PartialAlter - - ! : typeclass_instances.
Instance: Params (@partial_alter) 4.
Arguments partial_alter _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [dom C m] should yield the domain of [m]. That is a finite
collection of type [C] that contains the keys that are a member of [m]. *)
Class Dom (M C : Type) := dom: M → C.
Hint Mode Dom ! ! : typeclass_instances.
Instance: Params (@dom) 3.
Arguments dom : clear implicits.
Arguments dom {_} _ {_} !_ / : simpl nomatch, assert.

(** The function [merge f m1 m2] should merge the maps [m1] and [m2] by
constructing a new map whose value at key [k] is [f (m1 !! k) (m2 !! k)].*)
Class Merge (M : Type → Type) :=
  merge: ∀ {A B C}, (option A → option B → option C) → M A → M B → M C.
Hint Mode Merge ! : typeclass_instances.
Instance: Params (@merge) 4.
Arguments merge _ _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

(** The function [union_with f m1 m2] is supposed to yield the union of [m1]
and [m2] using the function [f] to combine values of members that are in
both [m1] and [m2]. *)
Class UnionWith (A M : Type) :=
  union_with: (A → A → option A) → M → M → M.
Hint Mode UnionWith - ! : typeclass_instances.
Instance: Params (@union_with) 3.
Arguments union_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

(** Similarly for intersection and difference. *)
Class IntersectionWith (A M : Type) :=
  intersection_with: (A → A → option A) → M → M → M.
Hint Mode IntersectionWith - ! : typeclass_instances.
Instance: Params (@intersection_with) 3.
Arguments intersection_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

Class DifferenceWith (A M : Type) :=
  difference_with: (A → A → option A) → M → M → M.
Hint Mode DifferenceWith - ! : typeclass_instances.
Instance: Params (@difference_with) 3.
Arguments difference_with {_ _ _} _ !_ !_ / : simpl nomatch, assert.

Definition intersection_with_list `{IntersectionWith A M}
  (f : A → A → option A) : M → list M → M := fold_right (intersection_with f).
Arguments intersection_with_list _ _ _ _ _ !_ / : assert.

Class LookupE (E K A M : Type) := lookupE: E → K → M → option A.
Hint Mode LookupE - - - ! : typeclass_instances.
Instance: Params (@lookupE) 6.
Notation "m !!{ Γ } i" := (lookupE Γ i m)
  (at level 20, format "m  !!{ Γ }  i") : stdpp_scope.
Notation "(!!{ Γ } )" := (lookupE Γ) (only parsing, Γ at level 1) : stdpp_scope.
Arguments lookupE _ _ _ _ _ _ !_ !_ / : simpl nomatch, assert.

Class InsertE (E K A M : Type) := insertE: E → K → A → M → M.
Hint Mode InsertE - - - ! : typeclass_instances.
Instance: Params (@insertE) 6.
Notation "<[ k := a ]{ Γ }>" := (insertE Γ k a)
  (at level 5, right associativity, format "<[ k := a ]{ Γ }>") : stdpp_scope.
Arguments insertE _ _ _ _ _ _ !_ _ !_ / : simpl nomatch, assert.


(** * Axiomatization of collections *)
(** The class [SimpleCollection A C] axiomatizes a collection of type [C] with
elements of type [A]. *)
Class SimpleCollection A C `{ElemOf A C,
    Empty C, Singleton A C, Union C} : Prop := {
  not_elem_of_empty (x : A) : x ∉ ∅;
  elem_of_singleton (x y : A) : x ∈ {[ y ]} ↔ x = y;
  elem_of_union X Y (x : A) : x ∈ X ∪ Y ↔ x ∈ X ∨ x ∈ Y
}.
Class Collection A C `{ElemOf A C, Empty C, Singleton A C,
    Union C, Intersection C, Difference C} : Prop := {
  collection_simple :>> SimpleCollection A C;
  elem_of_intersection X Y (x : A) : x ∈ X ∩ Y ↔ x ∈ X ∧ x ∈ Y;
  elem_of_difference X Y (x : A) : x ∈ X ∖ Y ↔ x ∈ X ∧ x ∉ Y
}.

(** We axiomative a finite collection as a collection whose elements can be
enumerated as a list. These elements, given by the [elements] function, may be
in any order and should not contain duplicates. *)
Class Elements A C := elements: C → list A.
Hint Mode Elements - ! : typeclass_instances.
Instance: Params (@elements) 3.

(** We redefine the standard library's [In] and [NoDup] using type classes. *)
Inductive elem_of_list {A} : ElemOf A (list A) :=
  | elem_of_list_here (x : A) l : x ∈ x :: l
  | elem_of_list_further (x y : A) l : x ∈ l → x ∈ y :: l.
Existing Instance elem_of_list.

Lemma elem_of_list_In {A} (l : list A) x : x ∈ l ↔ In x l.
Proof.
  split.
  - induction 1; simpl; auto.
  - induction l; destruct 1; subst; constructor; auto.
Qed.

Inductive NoDup {A} : list A → Prop :=
  | NoDup_nil_2 : NoDup []
  | NoDup_cons_2 x l : x ∉ l → NoDup l → NoDup (x :: l).

Lemma NoDup_ListNoDup {A} (l : list A) : NoDup l ↔ List.NoDup l.
Proof.
  split.
  - induction 1; constructor; rewrite <-?elem_of_list_In; auto.
  - induction 1; constructor; rewrite ?elem_of_list_In; auto.
Qed.

(** Decidability of equality of the carrier set is admissible, but we add it
anyway so as to avoid cycles in type class search. *)
Class FinCollection A C `{ElemOf A C, Empty C, Singleton A C, Union C,
    Intersection C, Difference C, Elements A C, EqDecision A} : Prop := {
  fin_collection :>> Collection A C;
  elem_of_elements X x : x ∈ elements X ↔ x ∈ X;
  NoDup_elements X : NoDup (elements X)
}.
Class Size C := size: C → nat.
Hint Mode Size ! : typeclass_instances.
Arguments size {_ _} !_ / : simpl nomatch, assert.
Instance: Params (@size) 2.

(** The class [CollectionMonad M] axiomatizes a type constructor [M] that can be
used to construct a collection [M A] with elements of type [A]. The advantage
of this class, compared to [Collection], is that it also axiomatizes the
the monadic operations. The disadvantage, is that not many inhabits are
possible (we will only provide an inhabitant using unordered lists without
duplicates removed). More interesting implementations typically need
decidability of equality, or a total order on the elements, which do not fit
in a type constructor of type [Type → Type]. *)
Class CollectionMonad M `{∀ A, ElemOf A (M A),
    ∀ A, Empty (M A), ∀ A, Singleton A (M A), ∀ A, Union (M A),
    !MBind M, !MRet M, !FMap M, !MJoin M} : Prop := {
  collection_monad_simple A :> SimpleCollection A (M A);
  elem_of_bind {A B} (f : A → M B) (X : M A) (x : B) :
    x ∈ X ≫= f ↔ ∃ y, x ∈ f y ∧ y ∈ X;
  elem_of_ret {A} (x y : A) : x ∈ mret y ↔ x = y;
  elem_of_fmap {A B} (f : A → B) (X : M A) (x : B) :
    x ∈ f <$> X ↔ ∃ y, x = f y ∧ y ∈ X;
  elem_of_join {A} (X : M (M A)) (x : A) : x ∈ mjoin X ↔ ∃ Y, x ∈ Y ∧ Y ∈ X
}.

(** The function [fresh X] yields an element that is not contained in [X]. We
will later prove that [fresh] is [Proper] with respect to the induced setoid
equality on collections. *)
Class Fresh A C := fresh: C → A.
Hint Mode Fresh - ! : typeclass_instances.
Instance: Params (@fresh) 3.
Class FreshSpec A C `{ElemOf A C,
    Empty C, Singleton A C, Union C, Fresh A C} : Prop := {
  fresh_collection_simple :>> SimpleCollection A C;
  fresh_proper_alt X Y : (∀ x, x ∈ X ↔ x ∈ Y) → fresh X = fresh Y;
  is_fresh (X : C) : fresh X ∉ X
}.

(** * Miscellaneous *)
Class Half A := half: A → A.
Hint Mode Half ! : typeclass_instances.
Notation "½" := half : stdpp_scope.
Notation "½*" := (fmap (M:=list) half) : stdpp_scope.

(** * Notations for lattices. *)
(** SqSubsetEq registers the "canonical" partial order for a type, and is used
for the \sqsubseteq symbol. *)
Class SqSubsetEq A := sqsubseteq: relation A.
Hint Mode SqSubsetEq ! : typeclass_instances.
Instance: Params (@sqsubseteq) 2.
Infix "⊑" := sqsubseteq (at level 70) : stdpp_scope.
Notation "(⊑)" := sqsubseteq (only parsing) : stdpp_scope.
Notation "( x ⊑)" := (sqsubseteq x) (only parsing) : stdpp_scope.
Notation "(⊑ y )" := (λ x, sqsubseteq x y) (only parsing) : stdpp_scope.
Instance sqsubseteq_rewrite `{SqSubsetEq A} : RewriteRelation (⊑).

Class Meet A := meet: A → A → A.
Hint Mode Meet ! : typeclass_instances.
Instance: Params (@meet) 2.
Infix "⊓" := meet (at level 40) : stdpp_scope.
Notation "(⊓)" := meet (only parsing) : stdpp_scope.
Notation "( x ⊓)" := (meet x) (only parsing) : stdpp_scope.
Notation "(⊓ y )" := (λ x, meet x y) (only parsing) : stdpp_scope.

Class Join A := join: A → A → A.
Hint Mode Join ! : typeclass_instances.
Instance: Params (@join) 2.
Infix "⊔" := join (at level 50) : stdpp_scope.
Notation "(⊔)" := join (only parsing) : stdpp_scope.
Notation "( x ⊔)" := (join x) (only parsing) : stdpp_scope.
Notation "(⊔ y )" := (λ x, join x y) (only parsing) : stdpp_scope.

Class Top A := top : A.
Hint Mode Top ! : typeclass_instances.
Notation "⊤" := top : stdpp_scope.

Class Bottom A := bottom : A.
Hint Mode Bottom ! : typeclass_instances.
Notation "⊥" := bottom : stdpp_scope.
