Local Set Warnings "-notation-overridden".

From mathcomp Require Import ssreflect eqtype ssralg ssrnat ssrbool.

From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.montgomery_rec.
From Tweetnacl Require Import Low.Prep_n.
From Tweetnacl Require Import Low.Unpack25519.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Mid.Inv25519.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Prep_n.
From Tweetnacl Require Import Instances.
From Tweetnacl Require Import Mid.Crypto_Scalarmult.
From Tweetnacl Require Import Low.Crypto_Scalarmult.
From Tweetnacl Require Import Low.Crypto_Scalarmult_.


From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_Fp_incl_Fp2.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.

Local Open Scope Z.


Definition decodeScalar25519 (l: list Z) : Z := 
  ZofList 8 (clamp l).

Definition decodeUCoordinate (l: list Z) : Z :=
  ZofList 8 (upd_nth 31 l (Z.land (nth 31 l 0) 127)).

Definition encodeUCoordinate (x: Z) : list Z := 
  ListofZ32 8 x.

Definition RFC (n: list Z) (p: list Z) : list Z :=
  let k := decodeScalar25519 n in
  let u := decodeUCoordinate p in
  let t := montgomery_rec
    255  (* iterate 255 times *)
    k    (* clamped n         *)
    1    (* x_2                *)
    u    (* x_3                *)
    0    (* z_2                *)
    1    (* z_3                *)
    0    (* dummy             *)
    0    (* dummy             *)
    u    (* x_1                *) in
  let a := get_a t in
  let c := get_c t in
  let o := ZPack25519 (Z.mul a (ZInv25519 c))
  in encodeUCoordinate o.

Lemma Crypto_Scalarmult_RFC_eq : forall n p,
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) n ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) p ->
  Crypto_Scalarmult n p = RFC n p.
Proof.
  move => n p Hln Hlp Hbn Hbp.
  rewrite /RFC /encodeUCoordinate /decodeUCoordinate /decodeScalar25519.
  rewrite Crypto_Scalarmult_Eq2 ; try assumption.
  apply f_equal.
  rewrite /ZCrypto_Scalarmult.
  rewrite Unpack25519'_Zlength.
  rewrite clamp_ZofList_eq_Zlength.
  reflexivity.
  all: assumption.
Qed.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Local Notation "'Fp2_x' P" := (Zmodp2.Zmodp2 (Zmodp.pi P) 0) (at level 30).
Local Notation "P '_x0'" := (val (Fp2_to_Fp (P #x0))) (at level 30).

Theorem RFC_Correct: forall (n p : list Z) (P:mc curve25519_Fp2_mcuType),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) n ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) p ->
  Fp2_x (decodeUCoordinate p) = P#x0 ->
  RFC n p = encodeUCoordinate ((P *+ (Z.to_nat (decodeScalar25519 n))) _x0).
Proof.
  move => n p P Hln Hlp HBn HBp.
  rewrite /encodeUCoordinate /decodeUCoordinate /decodeScalar25519.
  rewrite Unpack25519'_Zlength => //.
  rewrite -clamp_ZofList_eq_Zlength => //.
  move => HP.
  rewrite -(Crypto_Scalarmult_Correct n p P) => //.
  rewrite -Crypto_Scalarmult_RFC_eq => //.
  rewrite ListofZ32_ZofList_Zlength => //.
  apply Crypto_Scalarmult_Bound => //.
  apply Crypto_Scalarmult_Zlength => //.
Qed.

Close Scope ring_scope.

Local Close Scope Z.

