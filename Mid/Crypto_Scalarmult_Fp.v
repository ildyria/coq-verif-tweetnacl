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
From Tweetnacl Require Import Mid.Mod.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.

From stdpp Require Import list.

From Tweetnacl.High Require Import Zmodp opt_ladder_extr ladder curve25519.
From mathcomp Require Import ssreflect ssrbool eqtype ssralg.

From Tweetnacl.Mid Require Import Instances.
(* Definition Mod := (fun x => Z.modulo x (Z.pow 2 255 - 19)).

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
apply (fun n m => Z.of_nat (bitn (Z.to_nat (Z.of_nat m)) (Z.to_nat n))).
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Defined. *)

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
Defined. *)
(* 
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
Defined. *)

Definition Fp_Crypto_Scalarmult_rec_gen n p :=
  let t := montgomery_rec.montgomery_rec 255 n Zmodp.one p Zmodp.zero Zmodp.one Zmodp.zero Zmodp.zero p in
  (get_a t) * (get_c t)^-1.

Local Lemma v4inv : Zmodp.repr 4%:R^-1 = 43422033463993573283839119378257965444976244249615211514796594002967423614962.
Proof.
replace 43422033463993573283839119378257965444976244249615211514796594002967423614962 with (Zmodp.repr (Zmodp.pi (43422033463993573283839119378257965444976244249615211514796594002967423614962))).
2: by apply piK ; rewrite /betweenb /p -lock //=.
by congr (Zmodp.repr); apply GRing.mulr1_eq; apply/eqP; zmodp_compute; compute.
Qed.

Local Lemma curve25519_a_C121665 : (curve25519.a - 2%:R) / 4%:R = (Zmodp.pi C_121665).
Proof.
rewrite /a /C_121665.
apply/eqP.
zmodp_compute.
change ((486662 + 57896044618658097711785492504343953926634992332820282019728792003956564819947)
 `mod` 57896044618658097711785492504343953926634992332820282019728792003956564819949) with 486660.
rewrite v4inv.
compute.
reflexivity.
Qed.

Lemma get_a_Fp_Crypto_Scalarnult_eq m:
∀ (n : ℕ) (p a b c d e f : Zmodp.type), get_a (montgomery_rec.montgomery_rec m n a b c d e f p) =
get_a (opt_montgomery_rec_extr (K:=curve25519_finECUFieldType) curve25519_mcuType n m p a b c d).
Proof.
  induction m as [|m IHm] => n p a b c d e f //=.
  rewrite /cswap (Nat2Z.id n) (Nat2Z.id m).
  assert(Hnm:= bitnV n m);
  move:Hnm => /orP => Hnm;
  case Hnm => Hnm'.
  1: assert(bitn n m = 0%nat).
       by rewrite -nat_eqb_ssr_eq in Hnm' ; apply beq_nat_true.
  2: assert(bitn n m = 1%nat).
  2:   by rewrite -nat_eqb_ssr_eq in Hnm' ; apply beq_nat_true.
  all: by rewrite H => //=; erewrite IHm; rewrite curve25519_a_C121665.
Qed.

Lemma get_c_Fp_Crypto_Scalarnult_eq m:
∀ (n : ℕ) (p a b c d e f : Zmodp.type), get_c (montgomery_rec.montgomery_rec m n a b c d e f p) =
get_c (opt_montgomery_rec_extr (K:=curve25519_finECUFieldType) curve25519_mcuType n m p a b c d).
Proof.
  induction m as [|m IHm] => n p a b c d e f //=.
  rewrite /cswap (Nat2Z.id n) (Nat2Z.id m).
  assert(Hnm:= bitnV n m);
  move:Hnm => /orP => Hnm;
  case Hnm => Hnm'.
  1: assert(bitn n m = 0%nat).
       by rewrite -nat_eqb_ssr_eq in Hnm' ; apply beq_nat_true.
  2: assert(bitn n m = 1%nat).
  2:   by rewrite -nat_eqb_ssr_eq in Hnm' ; apply beq_nat_true.
  all: by rewrite H => //=; erewrite IHm; rewrite curve25519_a_C121665.
Qed.

Lemma Fp_Crypto_Scalarmult_rec_gen_equiv: forall n p,
  Fp_Crypto_Scalarmult_rec_gen n p = curve25519_ladder n p.
Proof.
  intros n p.
  rewrite /Fp_Crypto_Scalarmult_rec_gen
          /curve25519_ladder
          /opt_montgomery
          opt_montgomery_rec_equiv.
  f_equal; f_equal.
  apply get_a_Fp_Crypto_Scalarnult_eq.
  apply get_c_Fp_Crypto_Scalarnult_eq.
Qed.

Lemma abstract_fn_rev_eq_a_Fp : ∀ (m p : ℤ) (N : nat) (PP : Zmodp.type) (n pp:Z),
  0 ≤ m →
  val PP = pp ->
  Z.of_nat N = n ->
  modP (P (get_a (abstract_fn_rev m p N Zmodp.one PP Zmodp.zero Zmodp.one Zmodp.zero Zmodp.zero PP)))
  = modP (get_a (abstract_fn_rev m p n 1%Z pp 0%Z 1%Z 0%Z 0%Z pp)).
Proof.
  intros m p N PP n pp.
  intros Hm.
  intros HPP.
  intros HN.
  assert(Heq1:= @abstract_fn_rev_eq_a Zmodp.type nat Z id modP Z25519_Ops Z_Ops Z25519_Z_Eq m p).
  specialize Heq1 with N Zmodp.one PP Zmodp.zero Zmodp.one Zmodp.zero Zmodp.zero PP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /Z25519_Z_Eq.
  replace (val Zmodp.one) with 1%Z.
  replace (val Zmodp.zero) with 0%Z.
  rewrite HPP.
  rewrite -HN.
  trivial.
  move => //.
  rewrite /val.
  rewrite /Zmodp.one.
  rewrite /Zmodp_subType.
  simpl.
  symmetry.
  apply Z.mod_1_l.
  rewrite /Zmodp.p -lock.
reflexivity.
Qed.

Lemma abstract_fn_rev_eq_c_Fp : ∀ (m p : ℤ) (N : nat) (PP : Zmodp.type) (n pp:Z),
  0 ≤ m →
  val PP = pp ->
  Z.of_nat N = n ->
  modP (P (get_c (abstract_fn_rev m p N Zmodp.one PP Zmodp.zero Zmodp.one Zmodp.zero Zmodp.zero PP)))
  = modP (get_c (abstract_fn_rev m p n 1%Z pp 0%Z 1%Z 0%Z 0%Z pp)).
Proof.
  intros m p N PP n pp.
  intros Hm.
  intros HPP.
  intros HN.
  assert(Heq1:= @abstract_fn_rev_eq_c Zmodp.type nat Z id modP Z25519_Ops Z_Ops Z25519_Z_Eq m p).
  specialize Heq1 with N Zmodp.one PP Zmodp.zero Zmodp.one Zmodp.zero Zmodp.zero PP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /Z25519_Z_Eq.
  replace (val Zmodp.one) with 1%Z.
  replace (val Zmodp.zero) with 0%Z.
  rewrite HPP.
  rewrite -HN.
  trivial.
  move => //.
  rewrite /val.
  rewrite /Zmodp.one.
  rewrite /Zmodp_subType.
  simpl.
  symmetry.
  apply Z.mod_1_l.
  rewrite /Zmodp.p -lock.
  reflexivity.
Qed.



