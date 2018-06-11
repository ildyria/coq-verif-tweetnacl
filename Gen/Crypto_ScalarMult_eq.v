Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import UPIC.
From Tweetnacl.Gen Require Import UPIC_Prop.
From Tweetnacl.Gen Require Import montgomery_rec.
From Tweetnacl.Gen Require Import montgomery_rec_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev.
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

Theorem Crypto_ScalarMult_eq: forall (n p:T'),
  P' (CryptoScalarMult_rev n p) = CryptoScalarMult_rev (P' n) (P' p).
Proof.
  intros n p.
  rewrite /CryptoScalarMult_rev.
Admitted.

End CryptoScalarMult_eq.