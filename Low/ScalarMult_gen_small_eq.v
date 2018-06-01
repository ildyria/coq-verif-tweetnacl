Require Import Tweetnacl.Libs.Export.
Require Import ssreflect.
From Tweetnacl.Low Require Import ScalarMult_gen_small.
From Tweetnacl.Mid Require Import ScalarMult_gen_small.
From Tweetnacl.Low Require Import ScalarMult_rev_fn_gen.
From Tweetnacl.Mid Require Import ScalarMult_rev_fn_gen.

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

Lemma Zfa_eq_mod : forall r (a b c d e f x:Z),
  Mod (Zfa ZA ZM ZZub ZSq ZSel25519 r a b c d e f x) =
  Mod (Zfa ZA ZM ZZub ZSq ZSel25519 r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  rewrite /Zfa.
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

Lemma Zfb_eq_mod : forall r (a b c d e f x:Z),
  Mod (Zfb ZA ZM ZZub ZSq ZSel25519 r a b c d e f x) =
  Mod (Zfb ZA ZM ZZub ZSq ZSel25519 r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  rewrite /Zfb.
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

Lemma Zfc_eq_mod : forall r (a b c d e f x:Z),
  Mod (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519 r a b c d e f x) =
  Mod (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519 r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  rewrite /Zfc.
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

Lemma Zfd_eq_mod : forall r (a b c d e f x:Z),
  Mod (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519 r a b c d e f x) =
  Mod (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519 r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  rewrite /Zfd.
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

Lemma fe_eq_Zfe : forall r (a b c d e f x:list Z),
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

Lemma Zfe_eq_mod : forall r (a b c d e f x:Z),
  Mod (Zfe ZA ZM ZZub ZSel25519 r a b c d e f x) =
  Mod (Zfe ZA ZM ZZub ZSel25519 r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  rewrite /Zfe.
  down ; symmetry ; rewrite Mod_ZA_eq ; f_equal ; f_equal;
  down ; symmetry ; down ; f_equal ; f_equal;
  down ; symmetry ; down ; propagate ; down ; reflexivity.
Qed.

Lemma ff_eq_Zff : forall r (a b c d e f x:list Z),
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

Lemma Zff_eq_mod : forall r (a b c d e f x:Z),
  Mod (Zff ZZub ZSq ZSel25519 r a b c d e f x) =
  Mod (Zff ZZub ZSq ZSel25519 r (Mod a) (Mod b) (Mod c) (Mod d) (Mod e) (Mod f) (Mod x)).
Proof.
  intros.
  rewrite /Zff.
  down ; symmetry ; rewrite Mod_ZSq_eq ; f_equal ; f_equal.
  down ; symmetry ; down ; f_equal ; f_equal ; propagate ; down ; reflexivity.
Qed.

Local Lemma abstract_fn_eq_Z_ind_step : forall x : ℤ,
0 <= x ->
(forall (p : ℤ) (z a b c d e f x0 a' b' c' d' e' f' : list ℤ) (a'' b'' c'' d'' e'' f'' : ℤ),
(a', b', c', d', e', f') = abstract_fn_rev (fa A M Zub Sq Sel25519) (fb A M Zub Sq Sel25519) (fc A M Zub Sq _121665 Sel25519)
   (fd A M Zub Sq _121665 Sel25519) (fe A M Zub Sel25519) (ff Zub Sq Sel25519) getbit x p z a b c d e f x0 ->
(a'', b'', c'', d'', e'', f'') = Zabstract_fn_rev (Zfa ZA ZM ZZub ZSq ZSel25519) (Zfb ZA ZM ZZub ZSq ZSel25519)
   (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519) (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519) (Zfe ZA ZM ZZub ZSel25519)
   (Zff ZZub ZSq ZSel25519) Zgetbit x p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x0) ->
 Mod (P a') = Mod a'' /\
 Mod (P b') = Mod b'' /\
 Mod (P c') = Mod c'' /\ Mod (P d') = Mod d'' /\ Mod (P e') = Mod e'' /\ Mod (P f') = Mod f'') ->
forall (p : ℤ) (z a b c d e f x0 a' b' c' d' e' f' : list ℤ) (a'' b'' c'' d'' e'' f'' : ℤ),
(a', b', c', d', e', f') = abstract_fn_rev (fa A M Zub Sq Sel25519) (fb A M Zub Sq Sel25519) (fc A M Zub Sq _121665 Sel25519)
  (fd A M Zub Sq _121665 Sel25519) (fe A M Zub Sel25519) (ff Zub Sq Sel25519) getbit 
  (Z.succ x) p z a b c d e f x0 ->
(a'', b'', c'', d'', e'', f'') = Zabstract_fn_rev (Zfa ZA ZM ZZub ZSq ZSel25519) (Zfb ZA ZM ZZub ZSq ZSel25519)
  (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519) (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519) (Zfe ZA ZM ZZub ZSel25519)
  (Zff ZZub ZSq ZSel25519) Zgetbit (Z.succ x) p (P z) (P a) (P b) (P c) (P d) (P e) (P f) 
  (P x0) ->
Mod (P a') = Mod a'' /\
Mod (P b') = Mod b'' /\
Mod (P c') = Mod c'' /\ Mod (P d') = Mod d'' /\ Mod (P e') = Mod e'' /\ Mod (P f') = Mod f''.
Proof.
  move=> m Hm IHm.
  move=> p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f''.
  change (Z.succ m) with (m + 1).
  rewrite abstract_fn_rev_equation Zabstract_fn_rev_equation.
  replace (m + 1 - 1) with m by omega.
  match goal with
    | [ |- context[abstract_fn_rev ?FA ?FB ?FC ?FD ?FE ?FF ?G ?m ?p ?z ?a ?b ?c ?d ?e ?f ?x ]] => 
  remember (abstract_fn_rev FA FB FC FD FE FF G m p z a b c d e f x) as k'
  end.
  match goal with
    | [ |- context[Zabstract_fn_rev ?FA ?FB ?FC ?FD ?FE ?FF ?G ?m ?p ?z ?a ?b ?c ?d ?e ?f ?x ]] => 
  remember (Zabstract_fn_rev FA FB FC FD FE FF G m p z a b c d e f x) as k''
  end.
  destruct k' as (((((a0',b0'),c0'),d0'),e0'),f0').
  destruct k'' as (((((a0'',b0''),c0''),d0''),e0''),f0'').
  replace (m + 1 <=? 0) with false.
  2: symmetry ; apply Z.leb_gt ; omega.
  move=> Heq';inversion Heq'.
  move=> Heq'';inversion Heq''.
  assert(Ht:= IHm p z a b c d e f x a0' b0' c0' d0' e0' f0' a0'' b0'' c0'' d0'' e0'' f0'' Heqk' Heqk'').
  jauto_set.
  1: rewrite -fa_eq_Zfa getbit_eq Zfa_eq_mod ; symmetry ; rewrite Zfa_eq_mod.
  2: rewrite -fb_eq_Zfb getbit_eq Zfb_eq_mod ; symmetry ; rewrite Zfb_eq_mod.
  3: rewrite -fc_eq_Zfc getbit_eq Zfc_eq_mod ; symmetry ; rewrite Zfc_eq_mod.
  4: rewrite -fd_eq_Zfd getbit_eq Zfd_eq_mod ; symmetry ; rewrite Zfd_eq_mod.
  5: rewrite -fe_eq_Zfe getbit_eq Zfe_eq_mod ; symmetry ; rewrite Zfe_eq_mod.
  6: rewrite -ff_eq_Zff getbit_eq Zff_eq_mod ; symmetry ; rewrite Zff_eq_mod.
  all: symmetry ; f_equal ; f_equal ; assumption.
Admitted.

Lemma abstract_fn_eq_Zabstract_fn : forall m p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f'',
  0 <= m ->
  (a',b',c',d',e',f') = (abstract_fn_rev (fa A M Zub Sq Sel25519)
                      (fb A M Zub Sq Sel25519)
                      (fc A M Zub Sq _121665 Sel25519)
                      (fd A M Zub Sq _121665 Sel25519)
                      (fe A M Zub Sel25519)
                      (ff Zub Sq Sel25519)
                      getbit m p z a b c d e f x) -> 
  (a'',b'',c'',d'',e'',f'') = (Zabstract_fn_rev (Zfa ZA ZM ZZub ZSq ZSel25519)
                       (Zfb ZA ZM ZZub ZSq ZSel25519)
                       (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519)
                       (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519)
                       (Zfe ZA ZM ZZub ZSel25519)
                       (Zff ZZub ZSq ZSel25519)
                       Zgetbit m p
                       (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x))
 ->
  Mod (P a') = Mod a'' /\
  Mod (P b') = Mod b'' /\
  Mod (P c') = Mod c'' /\
  Mod (P d') = Mod d'' /\
  Mod (P e') = Mod e'' /\
  Mod (P f') = Mod f''.
Proof.
  intros m p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f'' Hm.
  gen a'' b'' c'' d'' e'' f''.
  gen a' b' c' d' e' f'.
  gen p z a b c d e f x.
  apply (natlike_ind (fun m => forall (p : ℤ) (z a b c d e f x a' b' c' d' e' f' : list ℤ) (a'' b'' c'' d'' e'' f'' : ℤ),
(a', b', c', d', e', f') =
abstract_fn_rev (fa A M Zub Sq Sel25519) (fb A M Zub Sq Sel25519) (fc A M Zub Sq _121665 Sel25519)
  (fd A M Zub Sq _121665 Sel25519) (fe A M Zub Sel25519) (ff Zub Sq Sel25519) getbit m p z a b c d e f x ->
(a'', b'', c'', d'', e'', f'') =
Zabstract_fn_rev (Zfa ZA ZM ZZub ZSq ZSel25519) (Zfb ZA ZM ZZub ZSq ZSel25519)
  (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519) (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519) (Zfe ZA ZM ZZub ZSel25519)
  (Zff ZZub ZSq ZSel25519) Zgetbit m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x) ->
Mod (P a') = Mod a'' /\
Mod (P b') = Mod b'' /\
Mod (P c') = Mod c'' /\ Mod (P d') = Mod d'' /\ Mod (P e') = Mod e'' /\ Mod (P f') = Mod f'')).

  3: omega.
  move=> p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f''.
  rewrite abstract_fn_rev_equation Zabstract_fn_rev_equation Zle_imp_le_bool ; try omega; go.
  apply abstract_fn_eq_Z_ind_step.
Qed.

Lemma abstract_fn_eq_Zabstract_fn' : forall m p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f'',
  0 <= m ->
  (a',b',c',d',e',f') = (abstract_fn_rev (fa A M Zub Sq Sel25519)
                      (fb A M Zub Sq Sel25519)
                      (fc A M Zub Sq _121665 Sel25519)
                      (fd A M Zub Sq _121665 Sel25519)
                      (fe A M Zub Sel25519)
                      (ff Zub Sq Sel25519)
                      getbit m p z a b c d e f x) -> 
  (a'',b'',c'',d'',e'',f'') = (Zabstract_fn_rev (Zfa ZA ZM ZZub ZSq ZSel25519)
                       (Zfb ZA ZM ZZub ZSq ZSel25519)
                       (Zfc ZA ZM ZZub ZSq Z_121665 ZSel25519)
                       (Zfd ZA ZM ZZub ZSq Z_121665 ZSel25519)
                       (Zfe ZA ZM ZZub ZSel25519)
                       (Zff ZZub ZSq ZSel25519)
                       Zgetbit m p
                       (Mod (P z)) (Mod (P a)) (Mod (P b)) (Mod (P c)) (Mod (P d)) (Mod (P e)) (Mod (P f)) (Mod (P x)))
 ->
  Mod (P a') = Mod a'' /\
  Mod (P b') = Mod b'' /\
  Mod (P c') = Mod c'' /\
  Mod (P d') = Mod d'' /\
  Mod (P e') = Mod e'' /\
  Mod (P f') = Mod f''.
Proof.
  intros m p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f'' Hm.
  gen a'' b'' c'' d'' e'' f''.
  gen a' b' c' d' e' f'.
  gen p z a b c d e f x.
  pattern m.
  eapply natlike_ind.
  3: omega.
  move=> p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f''.
  rewrite abstract_fn_rev_equation Zabstract_fn_rev_equation Zle_imp_le_bool ; try omega; go.
  clear m Hm.
  move=> m Hm IHm.
  move=> p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f''.
  change (Z.succ m) with (m + 1).
  rewrite abstract_fn_rev_equation Zabstract_fn_rev_equation.
  replace (m + 1 - 1) with m by omega.
  match goal with
    | [ |- context[abstract_fn_rev ?FA ?FB ?FC ?FD ?FE ?FF ?G ?m ?p ?z ?a ?b ?c ?d ?e ?f ?x ]] => 
  remember (abstract_fn_rev FA FB FC FD FE FF G m p z a b c d e f x) as k'
  end.
  match goal with
    | [ |- context[Zabstract_fn_rev ?FA ?FB ?FC ?FD ?FE ?FF ?G ?m ?p ?z ?a ?b ?c ?d ?e ?f ?x ]] => 
  remember (Zabstract_fn_rev FA FB FC FD FE FF G m p z a b c d e f x) as k''
  end.
  destruct k' as (((((a0',b0'),c0'),d0'),e0'),f0').
  destruct k'' as (((((a0'',b0''),c0''),d0''),e0''),f0'').
  replace (m + 1 <=? 0) with false.
  2: symmetry ; apply Z.leb_gt ; omega.
  move=> Heq' Heq''.
  assert(Ht:= IHm p z a b c d e f x a0' b0' c0' d0' e0' f0' a0'' b0'' c0'' d0'' e0'' f0'' Heqk' Heqk'').
  jauto_set.
Admitted.


Close Scope Z.

End ScalarRec.
