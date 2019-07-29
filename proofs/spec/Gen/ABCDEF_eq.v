From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import ABCDEF.
Require Import ssreflect.

Open Scope Z.

Section ABCDEF_Eq_Prop.

Context {T : Type}.
Context {T' : Type}.
Context {U : Type}.
Context (ModT : T -> T).
Context (Mod : U -> U).
Context {TO : Ops T T' ModT}.
Context {UO : Ops U U Mod}.
Context {UTO : @Ops_Mod_P T T' U Mod ModT TO UO}.

(*
Variable P : T -> U.
Variable Mod :U -> U.

Variable A_eq : forall a b, Mod (P (A a b)) = Mod (A (P a) (P b)).
Variable M_eq : forall a b, Mod (P (M a b)) = Mod (M (P a) (P b)).
Variable Zub_eq : forall a b,  Mod (P (Zub a b)) = Mod (Zub (P a) (P b)).
Variable Sq_eq : forall a,  Mod (P (Sq a)) = Mod (Sq (P a)).
Variable _121665_eq : Mod (P _121665) = Mod (_121665).
Variable Sel25519_eq : forall b p q,  Mod (P (Sel25519 b p q)) = Mod (Sel25519 b (P p) (P q)).
Variable getbit_eq : forall i p,  getbit i p = getbit i (P p).

Variable Mod_ZSel25519_eq : forall b p q,  Mod (Sel25519 b p q) = Sel25519 b (Mod p) (Mod q).
Variable Mod_ZA_eq : forall p q,  Mod (A p q) = Mod (A (Mod p) (Mod q)).
Variable Mod_ZM_eq : forall p q,  Mod (M p q) = Mod (M (Mod p) (Mod q)).
Variable Mod_ZZub_eq : forall p q,  Mod (Zub p q) = Mod (Zub (Mod p) (Mod q)).
Variable Mod_ZSq_eq : forall p,  Mod (Sq p) = Mod (Sq (Mod p)).
Variable Mod_red : forall p,  Mod (Mod p) = (Mod p).
*)
Local Ltac propagate := repeat match goal with
    | _ => rewrite A_eq
    | _ => rewrite M_eq
    | _ => rewrite Zub_eq
    | _ => rewrite Sq_eq
    | _ => rewrite C_121665_eq
    | _ => rewrite Sel25519_eq
    | _ => rewrite Mod_ZSel25519_eq
    | _ => rewrite Getbit_eq
  end.

Local Ltac down := match goal with
    | _ => rewrite !Mod_red
    | _ => rewrite Mod_ZM_eq
    | _ => rewrite Mod_ZA_eq
    | _ => rewrite Mod_ZZub_eq
    | _ => rewrite Mod_ZSq_eq
  end.

Lemma fa_eq : forall r (a b c d e f x:T),
  Mod (Gen.fa r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (Gen.fa r a b c d e f x)).
Proof.
  intros.
  unfold Gen.fa.
  propagate.
  f_equal.
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  reflexivity.
  down ; symmetry ; rewrite Mod_ZSq_eq ; propagate.
  f_equal ; f_equal ; down ; symmetry ; down ; propagate.
  f_equal ; f_equal ; down ; symmetry ; down ; propagate;
  f_equal ; f_equal ; down ; symmetry ; down ; propagate;
  reflexivity.
Qed.

Lemma fa_eq_mod : forall r (a b c d e f x:U),
  Mod (Gen.fa r a b c d e f x) =
  Mod (Gen.fa r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  unfold Gen.fa.
  propagate.
  f_equal.
  down ; symmetry; down.
  f_equal ; f_equal ; down ; symmetry ; rewrite Mod_ZSq_eq ;
  f_equal ; f_equal ; down ; symmetry ; rewrite ?Mod_ZSel25519_eq; reflexivity.
  down ; symmetry ; rewrite Mod_ZSq_eq.
  f_equal ; f_equal ; down ; symmetry ; rewrite Mod_ZA_eq.
  f_equal ; f_equal ; down ; symmetry ; down ;
  f_equal ; f_equal ; down ; symmetry ; down ;
  f_equal ; f_equal ; propagate ; down ; reflexivity.
Qed.

Lemma fb_eq : forall r (a b c d e f x:T),
  Mod (Gen.fb r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (Gen.fb r a b c d e f x)).
Proof.
  intros.
  unfold Gen.fb.
  propagate.
  f_equal.
  down ; symmetry ; rewrite Mod_ZSq_eq ; propagate.
  f_equal ; f_equal ; down ; symmetry ; down ; propagate.
  f_equal ; f_equal ; down ; symmetry ; down ; propagate;
  f_equal ; f_equal ; down ; symmetry ; down ; propagate;
  reflexivity.
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  reflexivity.
Qed.

Lemma fb_eq_mod : forall r (a b c d e f x:U),
  Mod (Gen.fb r a b c d e f x) =
  Mod (Gen.fb r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  unfold Gen.fb.
  propagate.
  f_equal.
  down ; symmetry ; rewrite Mod_ZSq_eq.
  f_equal ; f_equal ; down ; symmetry ; rewrite Mod_ZA_eq.
  f_equal ; f_equal ; down ; symmetry ; down ;
  f_equal ; f_equal ; down ; symmetry ; down ;
  f_equal ; f_equal ; propagate ; down ; reflexivity.
  down ; symmetry; down.
  f_equal ; f_equal ; down ; symmetry ; rewrite Mod_ZSq_eq ;
  f_equal ; f_equal ; down ; symmetry ; rewrite ?Mod_ZSel25519_eq; reflexivity.
Qed.

Lemma fc_eq : forall r (a b c d e f x:T),
  Mod (Gen.fc r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (Gen.fc r a b c d e f x)).
Proof.
  intros.
  unfold Gen.fc.
  propagate.
  f_equal.
  1 : {
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  rewrite Mod_ZSq_eq; f_equal ; f_equal;
  propagate ; down ; propagate ; reflexivity.
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
  2: rewrite Mod_ZSq_eq.
  all: f_equal ; f_equal ; propagate ; down ; symmetry; down;
  f_equal ; f_equal ; propagate ; down; try reflexivity;
  symmetry; rewrite Mod_ZSq_eq;
  f_equal ; f_equal ; propagate ; down ; symmetry ; down ; propagate ; reflexivity.
  }
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  f_equal ; f_equal ; down ; symmetry; rewrite Mod_ZZub_eq ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate ;
  f_equal ; f_equal ; down ; symmetry; down ; propagate ;
  reflexivity.
Qed.

Lemma fc_eq_mod : forall r (a b c d e f x:U),
  Mod (Gen.fc r a b c d e f x) =
  Mod (Gen.fc r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  unfold Gen.fc.
  propagate.
  f_equal.
  1 : {
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down.
  f_equal ; f_equal ; down ; symmetry; down;
  rewrite Mod_ZSq_eq; f_equal ; f_equal ;
  propagate ; reflexivity.
  rewrite Mod_ZA_eq ; f_equal ; f_equal ; down ; symmetry; down.
  2: rewrite Mod_ZSq_eq.
  all: f_equal ; f_equal ; propagate ; down ; try reflexivity.
  down ; symmetry; rewrite Mod_ZZub_eq ;
  f_equal ; f_equal ; down ; symmetry ; down ; rewrite Mod_ZSq_eq.
  1: rewrite Mod_ZA_eq.
  2: rewrite Mod_ZZub_eq.
  all: propagate ; down ; reflexivity.
  }
  down ; symmetry ; down.
  f_equal ; f_equal.
  2: down ; reflexivity.
  down ; symmetry ; rewrite Mod_ZSq_eq.
  f_equal ; f_equal ; down ; symmetry ; down ; rewrite Mod_ZZub_eq ;
  f_equal ; f_equal ; down ; symmetry ; down ;
  f_equal ; f_equal ; down.
  rewrite Mod_ZA_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; down ; reflexivity.
  rewrite Mod_ZZub_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; down ; reflexivity.
  rewrite Mod_ZZub_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; reflexivity.
  rewrite Mod_ZA_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; reflexivity.
Qed.

Lemma fd_eq : forall r (a b c d e f x:T),
  Mod (Gen.fd r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (Gen.fd r a b c d e f x)).
Proof.
  intros.
  unfold Gen.fd.
  propagate.
  f_equal.
  down ; symmetry; down; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  f_equal ; f_equal ; down ; symmetry; rewrite Mod_ZZub_eq ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate ;
  f_equal ; f_equal ; down ; symmetry; down ; propagate ;
  reflexivity.
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  rewrite Mod_ZSq_eq; f_equal ; f_equal;
  propagate ; down ; propagate ; reflexivity.
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
  2: rewrite Mod_ZSq_eq.
  all: f_equal ; f_equal ; propagate ; down ; symmetry; down;
  f_equal ; f_equal ; propagate ; down; try reflexivity;
  symmetry; rewrite Mod_ZSq_eq;
  f_equal ; f_equal ; propagate ; down ; symmetry ; down ; propagate ; reflexivity.
Qed.

Lemma fd_eq_mod : forall r (a b c d e f x:U),
  Mod (Gen.fd r a b c d e f x) =
  Mod (Gen.fd r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  unfold Gen.fd.
  propagate.
  f_equal.
  2 : {
  down ; symmetry; down; propagate.
  f_equal ; f_equal ; down ; symmetry; down.
  f_equal ; f_equal ; down ; symmetry; down;
  rewrite Mod_ZSq_eq; f_equal ; f_equal ;
  propagate ; reflexivity.
  rewrite Mod_ZA_eq ; f_equal ; f_equal ; down ; symmetry; down.
  2: rewrite Mod_ZSq_eq.
  all: f_equal ; f_equal ; propagate ; down ; try reflexivity.
  down ; symmetry; rewrite Mod_ZZub_eq ;
  f_equal ; f_equal ; down ; symmetry ; down ; rewrite Mod_ZSq_eq.
  1: rewrite Mod_ZA_eq.
  2: rewrite Mod_ZZub_eq.
  all: propagate ; down ; reflexivity.
  }
  down ; symmetry ; down.
  f_equal ; f_equal.
  2: down ; reflexivity.
  down ; symmetry ; rewrite Mod_ZSq_eq.
  f_equal ; f_equal ; down ; symmetry ; down ; rewrite Mod_ZZub_eq ;
  f_equal ; f_equal ; down ; symmetry ; down ;
  f_equal ; f_equal ; down.
  rewrite Mod_ZA_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; down ; reflexivity.
  rewrite Mod_ZZub_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; down ; reflexivity.
  rewrite Mod_ZZub_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; reflexivity.
  rewrite Mod_ZA_eq ; symmetry ; down ; f_equal ; f_equal ; propagate ; reflexivity.
Qed.

Lemma fe_eq : forall r (a b c d e f x:T),
  Mod (Gen.fe r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (Gen.fe r a b c d e f x)).
Proof.
  intros.
  unfold Gen.fe.
  propagate.
  down ; symmetry; rewrite Mod_ZA_eq ; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate ;
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
Qed.

Lemma fe_eq_mod : forall r (a b c d e f x:U),
  Mod (Gen.fe r a b c d e f x) =
  Mod (Gen.fe r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  unfold Gen.fe.
  down ; symmetry ; rewrite Mod_ZA_eq ; f_equal ; f_equal;
  down ; symmetry ; down ; f_equal ; f_equal;
  down ; symmetry ; down ; propagate ; down ; reflexivity.
Qed.

Lemma ff_eq : forall r (a b c d e f x:T),
  Mod (Gen.ff r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (Gen.ff r a b c d e f x)).
Proof.
  intros.
  unfold Gen.ff.
  propagate.
  down ; symmetry; rewrite Mod_ZSq_eq ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
  reflexivity.
Qed.

Lemma ff_eq_mod : forall r (a b c d e f x:U),
  Mod (Gen.ff r a b c d e f x) =
  Mod (Gen.ff r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  unfold Gen.ff.
  down ; symmetry ; rewrite Mod_ZSq_eq ; f_equal ; f_equal.
  down ; symmetry ; down ; f_equal ; f_equal ; propagate ; down ; reflexivity.
Qed.

End ABCDEF_Eq_Prop.

Close Scope Z.