From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Unpack25519.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import Inv25519.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Constant.

From Tweetnacl.Mid Require Import Prep_n.
From Tweetnacl.Mid Require Import ScalarMult_rev.
From Tweetnacl.Mid Require Import ScalarMult_gen_small.
From Tweetnacl.Mid Require Import ScalarMult_rev_fn_gen.



(* Definition Crypto_Scalarmult n p :=
  let a := get_a (montgomery_fn 255 254 (Zclamp n) 1 (Unpack25519 p) 0 1 0 0 (Unpack25519 p)) in
  let c := get_c (montgomery_fn 255 254 (Zclamp n) 1 (Unpack25519 p) 0 1 0 0 (Unpack25519 p)) in
  Pack25519 (M a (Inv25519 c)).
 *)
(* Definition Crypto_Scalarmult_rev n p :=
  let a := get_a (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  let c := get_c (montgomery_fn 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p)) in
  Pack25519 (M a (Inv25519 c))
 *)