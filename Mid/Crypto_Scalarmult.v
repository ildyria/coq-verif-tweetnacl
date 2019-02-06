From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.AMZubSqSel_Prop.
From Tweetnacl Require Import Gen.abstract_fn_rev.
From Tweetnacl Require Import Gen.montgomery_rec.
From Tweetnacl Require Import Gen.montgomery_rec_eq.
From Tweetnacl Require Import Mid.AMZubSqSel.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Mid.GetBit.
From Tweetnacl Require Import Mid.GetBit_bitn.
From Tweetnacl Require Import Mid.Prep_n.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Mid.Inv25519.
From Tweetnacl Require Import Mid.ScalarMult.
From Tweetnacl Require Import Mid.Crypto_Scalarmult_Fp.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg prime div.

Open Scope Z.

Section ZCrypto_Scalarmult_gen.

Context (Z_Ops : (Ops Z Z) (fun x => Z.modulo x ((Z.pow 2 255) - 19))).

Definition ZCrypto_Scalarmult_rev_gen n p :=
  let t := abstract_fn_rev 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

Definition ZCrypto_Scalarmult_rec_gen n p :=
  let t := montgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

End ZCrypto_Scalarmult_gen.

Local Instance Z_Ops : (Ops Z Z (fun x => Z.modulo x (Z.pow 2 255 - 19))) := {}.
Proof.
apply A.
apply M.
apply Zub.
apply Sq.
apply C_0.
apply C_1.
apply C_121665.
apply Sel25519.
apply Zgetbit.
intros b p q ; rewrite /Sel25519 ; flatten.
intros ; apply A_mod_eq.
intros ; apply M_mod_eq.
intros ; apply Zub_mod_eq.
intros ; apply Sq_mod_eq.
intros ; apply Zmod_mod.
Defined.


(* @Timmy this is the definition you want to prove correct with respect to your specifications *)
Definition ZCrypto_Scalarmult n p :=
  let t := Zmontgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

(* This is the equivalence between ladders defined as fn with type class and ladders defined as recursive *)
Theorem ZCrypto_Scalarmult_eq : forall (n p : Z),
  ZCrypto_Scalarmult n p = ZCrypto_Scalarmult_rev_gen Z_Ops n p.
Proof.
  intros.
  rewrite /ZCrypto_Scalarmult /ZCrypto_Scalarmult_rev_gen.
  rewrite /Zmontgomery_rec.
  replace (montgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)) with
  (montgomery_rec (S (Z.to_nat 254)) (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)).
  2: change (S (Z.to_nat 254)) with 255%nat.
  2: reflexivity.
  rewrite montgomery_rec_eq_fn_rev.
  2: omega.
  change (254 + 1) with 255.
  reflexivity.
Qed.

Local Instance Z25519_Ops : (Ops Zmodp.type nat id) := {}.
Proof.
apply Zmodp.add.
apply Zmodp.mul.
apply (fun x y => Zmodp.add x (Zmodp.opp y)).
apply (fun x => Zmodp.mul x x).
apply Zmodp.zero.
apply Zmodp.one.
apply (Zmodp.pi C_121665).
apply (fun b p q => if b =? 0 then p else q).
apply (fun n m => Z.of_nat (ladder.bitn (Z.to_nat (Z.of_nat m)) (Z.to_nat n))).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Defined.

(* Local Instance Z_Ops : (Ops Z Z Mod) := {}.
Proof.
apply A.
apply M.
apply Zub.
apply Sq.
apply C_0.
apply C_1.
apply C_121665.
apply Sel25519.
apply Zgetbit.
intros b p q ; rewrite /Sel25519 ; flatten.
intros ; apply A_mod_eq.
intros ; apply M_mod_eq.
intros ; apply Zub_mod_eq.
intros ; apply Sq_mod_eq.
intros ; apply Zmod_mod.
Defined.
 *)

Local Instance Z25519_Z_Eq : @Ops_Mod_P Zmodp.type nat Z Mod id Z25519_Ops Z_Ops := {
P := val;
P' := Z.of_nat
}.
Proof.
intros; simpl. rewrite /A /Mod /p -lock Zmod_mod. reflexivity.
intros; simpl. rewrite /M /Mod /p -lock Zmod_mod -Zcar25519_correct -Zcar25519_correct. reflexivity.
intros; simpl. rewrite /Zub /Mod /p -lock Zmod_mod.
rewrite -Zminus_mod_idemp_l.
change ((2 ^ 255 - 19) :𝓖𝓕) with 0%Z.
rewrite Zplus_mod_idemp_r.
f_equal.
intros; simpl. rewrite /Sq /M /Mod /p -lock Zmod_mod -Zcar25519_correct -Zcar25519_correct. reflexivity.
simpl; rewrite /C_121665 /p -lock. reflexivity.
simpl; rewrite /C_0 /p -lock. reflexivity.
simpl; rewrite /C_1 /p -lock. reflexivity.
intros; simpl.
rewrite /Mod /Sel25519 ; flatten.
intros; simpl.
apply Zgetbit_bitn.
Defined.
(* 
Lemma ZCrypto_Scalarmult_curve25519_ladder n x : (*(x : Zmodp.type) :*)
  ZCrypto_Scalarmult n x = val (curve25519_ladder (Z.to_nat (Zclamp n)) (Zmodp.pi x)).
Proof.
(* rewrite  *)
(* get_a (Zmontgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 x) 0 1 0 0 (ZUnpack25519 x)) :𝓖𝓕 *
((get_c (Zmontgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 x) 0 1 0 0 (ZUnpack25519 x)) :𝓖𝓕) ^ (2 ^ 255 - 21) :𝓖𝓕) :𝓖𝓕 

Lemma ZCrypto_Scalarmult_curve25519_ladder n x : (*(x : Zmodp.type) :*)
  ZCrypto_Scalarmult n x = val (curve25519_ladder (Z.to_nat (Zclamp n)) (Zmodp.pi x)).
 *)
rewrite /ZCrypto_Scalarmult.
rewrite -Fp_Crypto_Scalarmult_rec_gen_equiv.
(* rewrite /curve25519_ladder. *)
(* rewrite /opt_montgomery. *)
(* rewrite /ZCrypto_Scalarmult_rev_gen. *)
rewrite /ZPack25519.
rewrite /ZInv25519.
rewrite Zmult_mod.
rewrite pow_mod.
2: by compute.
rewrite /Zmontgomery_rec.
rewrite /Fp_Crypto_Scalarmult_rec_gen.
rewrite /val /Zmodp_subType.
rewrite -modZp /p -lock.
SearchAbout "/".
SearchAbout Zmodp.repr.
assert(case: (boolP (b == 0)) => [/eqP|] Hb)
SearchAbout div.
SearchAbout Znumtheory.rel_prime Znumtheory.prime.
assert(Znumtheory.prime (2 ^ 255 - 19)).
apply primo.
Check Znumtheory.rel_prime_le_prime.
Check Zp.Zorder_power_is_1.
SearchAbout Zp.Zorder.
SearchAbout Z.divide.
SearchAbout "^-1".
GRing.mulr1_eq.

SearchAbout Znumtheory.prime.
SearchAbout Zp.Zorder.
SearchAbout Z.div Z.pow.

Admitted.
 *)
Close Scope Z.
