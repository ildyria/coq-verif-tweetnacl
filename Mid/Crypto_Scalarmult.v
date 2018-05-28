From Tweetnacl.Libs Require Import Export.

From Tweetnacl.Low Require Import Get_abcdef.

From Tweetnacl.Mid Require Import Prep_n.
From Tweetnacl.Mid Require Import Unpack25519.
From Tweetnacl.Mid Require Import Pack25519.
From Tweetnacl.Mid Require Import Inv25519.
From Tweetnacl.Mid Require Import ScalarMult_rev.
From Tweetnacl.Mid Require Import ScalarMult_gen_small.
From Tweetnacl.Mid Require Import ScalarMult_rev_fn_gen.

Open Scope Z.

Definition ZCrypto_Scalarmult n p :=
  let a := get_a (Zmontgomery_fn 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)) in
  let c := get_c (Zmontgomery_fn 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)) in
  ZPack25519 (Z.mul a (ZInv25519 c)).

Close Scope Z.