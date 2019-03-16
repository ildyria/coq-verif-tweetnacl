From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From mathcomp Require Import ssreflect eqtype ssralg ssrnat.

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
From Tweetnacl.High Require Import curve25519.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl Require Import Mod.

(* short name for Tweetnacl_verif *)
Definition CSM := Crypto_Scalarmult.

Theorem CSM_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) n ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = val (curve25519_ladder (Z.to_nat (Zclamp (ZofList 8 n))) (Zmodp.pi (modP (ZUnpack25519 (ZofList 8 p))))).
Proof.
move => n p Hln Hlp HBn HBp.
rewrite -ZCrypto_Scalarmult_curve25519_ladder.
apply Crypto_Scalarmult_Eq => //.
Qed.

(* Theorem curve25519_ladder_ok (n : nat) x :
  (n < 2^255)%nat -> x != 0 ->
  forall (p : mc curve25519_mcuType), p#x0 = x -> curve25519_ladder n x = (p *+ n)#x0.
 *)
Open Scope ring_scope.
Import GRing.Theory.
Import ssrnat.
Local Notation "p '#x0'" := (point_x0 p) (at level 30).

Local Lemma Zclamp_istrue N: is_true (ssrnat.leq (S (Z.to_nat (Zclamp N))) (ssrnat.expn 2 255)).
Proof.
Admitted.
(* SearchAbout ssrnat.expn.
SearchAbout ssrnat.expn Nat.pow.
have := Zclamp_max N.
have := Zclamp_min N.
move: (Zclamp N) => M Hm.
rewrite Z2Nat.inj_lt => //.
have ->: (Z.to_nat (2^255) = Nat.pow 2 255)%nat.
rewrite -(Nat2Z.id (Nat.pow 2 255)%N).
apply f_equal.
symmetry.
have Hinj := inj_pow 2%N 255%N.
rewrite Hinj.
change (ℤ.ℕ 2) with 2.
change (ℤ.ℕ 255) with 255.
reflexivity.
move: (2^255)%nat => T.
move => H.
apply/ltP. => H.


move => ->.
change (2^255)%N with 57896044618658097711785492504343953926634992332820282019728792003956564819968%N.
Eval compute in (2^255).
apply f_equal.
rewrite /expn.
rewrite /expn_rec.
rewrite /iterop.
Search iterop.

Search expn Z.to_nat.
f_equal.
rewrite -Z_of_nat_to_nat_p.
Nat2Z.id
Z2Nat.id
SearchAbout Z.to_nat expn.
move/ltP => Hm.
Search Z.to_nat Z.lt.
omega.
//.
rewrite /Zclamp.
Eval compute in (Z.ones 255).
change (57896044618658097711785492504343953926634992332820282019728792003956564819960) with (Z.ones 255).
 *)
Theorem Crypto_Scalarmult_Correct: forall (n p:list Z) (P:mc curve25519_mcuType),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) n ->
  Forall (fun x => 0 <= x /\ x < 2 ^ 8) p ->
  (Zmodp.pi (modP (ZUnpack25519 (ZofList 8 p)))) = P#x0 ->
  ZofList 8 (Crypto_Scalarmult n p) = val ((P *+ (Z.to_nat (Zclamp (ZofList 8 n))))#x0).
Proof.
  move=> n p P Hn Hp Hbn Hbp HP.
  rewrite CSM_Eq //.
  f_equal.
  apply curve25519_ladder_ok => //.
  move: (ZofList 8 n) => N.
  apply Zclamp_istrue.
Admitted.
