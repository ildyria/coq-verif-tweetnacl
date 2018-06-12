(* Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import UPIC.
From Tweetnacl.Gen Require Import UPIC_Prop.
(* From Tweetnacl.Gen Require Import montgomery_rec. *)
(* From Tweetnacl.Gen Require Import montgomery_rec_eq. *)
From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import Crypto_ScalarMult.

Section CryptoScalarMult_eq.

Context {T : Type}.
Context {T' : Type}.
Context {O_T : Ops T T'}.
Context {O_ext_T : Ops_ext T T'}.

Context {U : Type}.
Context {O_U : Ops U U}.
Context {O_ext_U : Ops_ext U U}.

Context {O_MP_TU: @Ops_Mod_P T T' U O_T O_U}.
Context {OP_ext_TU: @Ops_ext_Mod_P T T' U O_U O_ext_T O_ext_U}.

Variable P_eq : forall p, AMZubSqSel_Prop.P p = P p.
Variable P'_eq : forall p, AMZubSqSel_Prop.P' p = P' p.

Theorem Crypto_ScalarMult_eq: forall (n p:T'),
  P' (CryptoScalarMult_rev n p) = CryptoScalarMult_rev (P' n) (P' p).
Proof.
  intros n p.
  rewrite /CryptoScalarMult_rev.
  rewrite Pack25519_eq.
  rewrite ?Mod_Pack25519_eq.
  rewrite -P_eq.
  rewrite M_eq.
  rewrite Mod_ZM_eq.
  symmetry.
  rewrite Mod_ZM_eq.
  symmetry.
  f_equal ; f_equal.
  {
  rewrite abstract_fn_rev_eq_a.
  2:omega.
  rewrite C_0_eq C_1_eq.
  rewrite ?P_eq ?P'_eq.
  rewrite Unpack25519_eq Clamp_eq.
  reflexivity.
  }
  {
  rewrite P_eq.
  rewrite Inv25519_eq.
  rewrite Inv25519_mod_eq.
  symmetry.
  rewrite Inv25519_mod_eq.
  f_equal ; f_equal.
  rewrite -P_eq.
  rewrite abstract_fn_rev_eq_c.
  2: omega.
  rewrite C_0_eq C_1_eq.
  rewrite ?P_eq ?P'_eq.
  rewrite Unpack25519_eq Clamp_eq.
  reflexivity.
  }
Qed.

End CryptoScalarMult_eq. *)