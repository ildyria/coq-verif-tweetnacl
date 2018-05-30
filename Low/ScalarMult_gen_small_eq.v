Require Import Tweetnacl.Libs.Export.
Require Import ssreflect.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Mid.ScalarMult_gen_small.

Section ScalarRec.

Open Scope Z.

Variable A : list Z -> list Z -> list Z.
Variable M : list Z -> list Z -> list Z.
Variable Zub : list Z -> list Z -> list Z.
Variable Sq : list Z -> list Z.
Variable _121665: list Z.
Variable Sel25519 : Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Variable ZA : Z -> Z -> Z.
Variable ZM : Z -> Z -> Z.
Variable ZZub : Z -> Z -> Z.
Variable ZSq : Z -> Z.
Variable Z_121665: Z.
Variable ZSel25519 : Z -> Z -> Z -> Z.
Variable Zgetbit : Z -> Z -> Z.

Variable P : list Z -> Z.
Variable Mod : Z -> Z.

Variable A_eq : forall a b, Mod (P (A a b)) = Mod (ZA (P a) (P b)).
Variable M_eq : forall a b, Mod (P (M a b)) = Mod (ZM (P a) (P b)).
Variable Zub_eq : forall a b,  Mod (P (Zub a b)) = Mod (ZZub (P a) (P b)).
Variable Sq_eq : forall a,  Mod (P (Sq a)) = Mod (ZSq (P a)).
Variable _121665_eq : Mod (P _121665) = Mod (Z_121665).
Variable Sel25519_eq : forall b p q,  Mod (P (Sel25519 b p q)) = Mod (ZSel25519 b (P p) (P q)).
Variable getbit_eq : forall i p,  getbit i p = Zgetbit i (P p).

Variable Mod_ZSel25519_eq : forall b p q,  Mod (ZSel25519 b p q) = ZSel25519 b (Mod p) (Mod q).
Variable Mod_ZA_eq : forall p q,  Mod (ZA p q) = Mod (ZA (Mod p) (Mod q)).
Variable Mod_ZM_eq : forall p q,  Mod (ZM p q) = Mod (ZM (Mod p) (Mod q)).
Variable Mod_ZZub_eq : forall p q,  Mod (ZZub p q) = Mod (ZZub (Mod p) (Mod q)).
Variable Mod_ZSq_eq : forall p,  Mod (ZSq p) = Mod (ZSq (Mod p)).
Variable Mod_red : forall p,  Mod (Mod p) = (Mod p).

Local Ltac propagate := repeat match goal with
    | _ => rewrite A_eq
    | _ => rewrite M_eq
    | _ => rewrite Zub_eq
    | _ => rewrite Sq_eq
    | _ => rewrite _121665_eq
    | _ => rewrite Sel25519_eq
    | _ => rewrite Mod_ZSel25519_eq
    | _ => rewrite getbit_eq
  end.

Local Ltac down := match goal with
    | _ => rewrite !Mod_red
    | _ => rewrite Mod_ZM_eq
    | _ => rewrite Mod_ZA_eq
    | _ => rewrite Mod_ZZub_eq
    | _ => rewrite Mod_ZSq_eq
  end.

Lemma fa_eq_Zfa : forall r (a b c d e f x:list Z),
  Mod (Zfa ZA ZM ZZub ZSq ZSel25519 r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (fa A M Zub Sq Sel25519 r a b c d e f x)).
Proof.
  intros.
  rewrite /Zfa /fa.
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

Lemma fb_eq_Zfb : forall r (a b c d e f x:list Z),
  Mod (Zfb ZA ZM ZZub ZSq ZSel25519 r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (fb A M Zub Sq Sel25519 r a b c d e f x)).
Proof.
  intros.
  rewrite /Zfb /fb.
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

Lemma fc_eq_Zfc : forall r (a b c d e f x:list Z),
  Mod (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519 r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (fc A M Zub Sq _121665 Sel25519 r a b c d e f x)).
Proof.
  intros.
  rewrite /Zfc /fc.
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

Lemma fd_eq_Zfd : forall r (a b c d e f x:list Z),
  Mod (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519 r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (fd A M Zub Sq _121665 Sel25519 r a b c d e f x)).
Proof.
  intros.
  rewrite /Zfd /fd.
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

Lemma fe_eq_Zfd : forall r (a b c d e f x:list Z),
  Mod (Zfe ZA ZM ZZub ZSel25519 r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (fe A M Zub Sel25519 r a b c d e f x)).
Proof.
  intros.
  rewrite /Zfe /fe.
  propagate.
  down ; symmetry; rewrite Mod_ZA_eq ; propagate.
  f_equal ; f_equal ; down ; symmetry; down ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate ;
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
Qed.

Lemma ff_eq_Zfd : forall r (a b c d e f x:list Z),
  Mod (Zff ZZub ZSq ZSel25519 r (P a) (P b) (P c) (P d) (P e) (P f) (P x)) =
  Mod (P (ff Zub Sq Sel25519 r a b c d e f x)).
Proof.
  intros.
  rewrite /Zff /ff.
  propagate.
  down ; symmetry; rewrite Mod_ZSq_eq ; propagate;
  f_equal ; f_equal ; down ; symmetry; down ; propagate.
  reflexivity.
Qed.

Close Scope Z.

End ScalarRec.
