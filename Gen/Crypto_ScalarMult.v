Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import UPIC.
From Tweetnacl.Gen Require Import montgomery_rec.
From Tweetnacl.Gen Require Import montgomery_rec_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev.

Section CryptoScalarMult.

Context {T : Type}.
Context {T' : Type}.
Context {OT : Ops T T'}.
Context {OP : Ops_ext T T'}.

Definition CryptoScalarMult_rec (n p:T') : T' :=
  let t := (montgomery_rec 255 (Clamp n) C_1 (Unpack25519 p) C_0 C_1 C_0 C_0 (Unpack25519 p)) in 
  let a := get_a t in
  let c := get_c t in
  Pack25519 (M a (Inv25519 c)).

Definition CryptoScalarMult_rev (n p: T') : T' :=
  let t := (abstract_fn_rev 255 254 (Clamp n) C_1 (Unpack25519 p) C_0 C_1 C_0 C_0 (Unpack25519 p)) in 
  let a := get_a t in
  let c := get_c t in
  Pack25519 (M a (Inv25519 c)).

Lemma CryptoScalarMult_eq : forall n p, CryptoScalarMult_rev n p = CryptoScalarMult_rec n p.
Proof.
  intros.
  rewrite /CryptoScalarMult_rev /CryptoScalarMult_rec.
  change (255) with (S (Z.to_nat 254)).
  rewrite montgomery_rec_eq_fn_rev.
  2: omega.
  reflexivity.
Qed.

End CryptoScalarMult.
