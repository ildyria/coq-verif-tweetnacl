From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Low Require Import Crypto_Scalarmult.
From Tweetnacl.Mid Require Import Crypto_Scalarmult.
From Tweetnacl.Gen Require Import AMZubSqSel_List.
From Tweetnacl.Low Require Import A.
From Tweetnacl.Low Require Import Z.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import S.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Prep_n.

From Tweetnacl.Mid Require Import Instances.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519.
From mathcomp Require Import ssreflect eqtype ssralg.
From Tweetnacl Require Import Mod.

(* short name for Tweetnacl_verif *)
Definition CSM := Crypto_Scalarmult.

Theorem CSM_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = val (curve25519_ladder (Z.to_nat (Zclamp (ZofList 8 n))) (Zmodp.pi (modP (ZUnpack25519 (ZofList 8 p))))).
Proof.
move => n p Hln Hlp HBn HBp.
rewrite -ZCrypto_Scalarmult_curve25519_ladder.
apply Crypto_Scalarmult_Eq => //.
apply ZofList_pos => //.
rewrite /ZList_pos.
eapply Forall_impl.
apply HBn.
intro x ; simpl ; omega.
Qed.