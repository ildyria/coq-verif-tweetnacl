Local Set Warnings "-notation-overridden".
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From mathcomp Require Import ssreflect eqtype ssralg ssrnat ssrbool.

From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Low Require Import Crypto_Scalarmult.
From Tweetnacl.Mid Require Import Crypto_Scalarmult.
From Tweetnacl.Mid Require Import Prep_n.
From Tweetnacl.Gen Require Import AMZubSqSel_List.
From Tweetnacl.Low Require Import A.
From Tweetnacl.Low Require Import Z.
From Tweetnacl.Low Require Import M.
From Tweetnacl.Low Require Import S.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Prep_n.
Require Import Znat.
Require Import ZArith.Zpow_facts.

From Tweetnacl.Mid Require Import Instances.

From Tweetnacl.High Require Import Zmodp.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import curve25519_Fp.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_Fp_incl_Fp2.
From Tweetnacl.High Require Import prime_and_legendre.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl Require Import Mod.

(* short name for Tweetnacl_verif *)
Definition CSM := Crypto_Scalarmult.

Lemma CSM_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) n ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = val (curve25519_Fp_ladder (Z.to_nat (Zclamp (ZofList 8 n))) (Zmodp.pi (ZUnpack25519 (ZofList 8 p)))).
Proof.
move => n p Hln Hlp HBn HBp.
rewrite -ZCrypto_Scalarmult_curve25519_ladder.
apply Crypto_Scalarmult_Eq => //.
Qed.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "p '/p'" := (Fp2_to_Fp p) (at level 40).

Local Lemma expn_pown : forall n x, Nat.pow x n = expn x n.
Proof.
  elim => [| n IHn] x /=.
  by rewrite expn0.
  rewrite expnS IHn.
  done.
Qed.

Local Lemma Zclamp_istrue N: is_true (ssrnat.leq (S (Z.to_nat (Zclamp N))) (ssrnat.expn 2 255)).
Proof.
have := Zclamp_max N.
have := Zclamp_min N.
move: (Zclamp N) => M Hm.
rewrite Z2Nat.inj_lt => //.
have ->: (Z.to_nat (2^255) = Nat.pow 2 255)%nat.
rewrite -(Nat2Z.id (Nat.pow 2 255)%N).
apply f_equal.
symmetry.
have -> := inj_pow 2%N 255%N => //.
rewrite expn_pown.
by move/ltP.
Qed.

Local Notation "'Fp2_x' P" := (Zmodp2.Zmodp2 (Zmodp.pi P) 0) (at level 30).
Local Notation "P '_x0'" := (val ((P )#x0 /p)) (at level 30).

Theorem Crypto_Scalarmult_Correct: forall (n p:list Z) (P:mc curve25519_Fp2_mcuType),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) n ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) p ->
  Fp2_x (ZUnpack25519 (ZofList 8 p)) = P#x0 ->
  ZofList 8 (Crypto_Scalarmult n p) = (P *+ (Z.to_nat (Zclamp (ZofList 8 n)))) _x0.
Proof.
  move=> n p P Hn Hp Hbn Hbp HP.
  rewrite CSM_Eq //.
  f_equal.
  apply curve25519_Fp2_ladder_ok => //.
  move: (ZofList 8 n) => N.
  apply Zclamp_istrue.
Qed.
