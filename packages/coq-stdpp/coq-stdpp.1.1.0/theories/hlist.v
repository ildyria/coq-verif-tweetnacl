(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import tactics.
Set Default Proof Using "Type".
Local Set Universe Polymorphism.

(* Not using [list Type] in order to avoid universe inconsistencies *)
Inductive tlist := tnil : tlist | tcons : Type → tlist → tlist.

Inductive hlist : tlist → Type :=
  | hnil : hlist tnil
  | hcons {A As} : A → hlist As → hlist (tcons A As).

Fixpoint tapp (As Bs : tlist) : tlist :=
  match As with tnil => Bs | tcons A As => tcons A (tapp As Bs) end.
Fixpoint happ {As Bs} (xs : hlist As) (ys : hlist Bs) : hlist (tapp As Bs) :=
  match xs with hnil => ys | hcons x xs => hcons x (happ xs ys) end.

Fixpoint hhead {A As} (xs : hlist (tcons A As)) : A :=
  match xs with hnil => () | hcons x _ => x end.
Fixpoint htail {A As} (xs : hlist (tcons A As)) : hlist As :=
  match xs with hnil => () | hcons _ xs => xs end.

Fixpoint hheads {As Bs} : hlist (tapp As Bs) → hlist As :=
  match As with
  | tnil => λ _, hnil
  | tcons A As => λ xs, hcons (hhead xs) (hheads (htail xs))
  end.
Fixpoint htails {As Bs} : hlist (tapp As Bs) → hlist Bs :=
  match As with
  | tnil => id
  | tcons A As => λ xs, htails (htail xs)
  end.

Fixpoint himpl (As : tlist) (B : Type) : Type :=
  match As with tnil => B | tcons A As => A → himpl As B end.

Definition hinit {B} (y : B) : himpl tnil B := y.
Definition hlam {A As B} (f : A → himpl As B) : himpl (tcons A As) B := f.
Arguments hlam _ _ _ _ _ / : assert.

Definition hcurry {As B} (f : himpl As B) (xs : hlist As) : B :=
  (fix go {As} xs :=
    match xs in hlist As return himpl As B → B with
    | hnil => λ f, f
    | hcons x xs => λ f, go xs (f x)
    end) _ xs f.
Coercion hcurry : himpl >-> Funclass.

Fixpoint huncurry {As B} : (hlist As → B) → himpl As B :=
  match As with
  | tnil => λ f, f hnil
  | tcons x xs => λ f, hlam (λ x, huncurry (f ∘ hcons x))
  end.

Lemma hcurry_uncurry {As B} (f : hlist As → B) xs : huncurry f xs = f xs.
Proof. by induction xs as [|A As x xs IH]; simpl; rewrite ?IH. Qed.

Fixpoint hcompose {As B C} (f : B → C) {struct As} : himpl As B → himpl As C :=
  match As with
  | tnil => f
  | tcons A As => λ g, hlam (λ x, hcompose f (g x))
  end.
