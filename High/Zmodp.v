Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice ssralg.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import curve25519_prime_cert.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope Z.

(* EqType for Z TODO: move to another file *)
Definition Z_of_natsum (s : nat + nat) : Z :=
  match s with
  | inl n => -Z.of_nat n
  | inr n => Z.of_nat n
  end.
Definition natsum_of_Z (x : Z) : nat + nat :=
  match x with
  | Z0 => inr 0%nat
  | Zpos p => inr (Pos.to_nat p)
  | Zneg p => inl (Pos.to_nat p)
  end.

Lemma natsum_of_ZK : cancel natsum_of_Z Z_of_natsum.
Proof.
case=> //= [|p]; first exact: positive_nat_Z.
by rewrite positive_nat_Z; apply: Pos2Z.opp_pos.
Qed.

Definition Z_eqMixin := CanEqMixin natsum_of_ZK.
Definition Z_countMixin := CanCountMixin natsum_of_ZK.
Definition Z_choiceMixin := CountChoiceMixin Z_countMixin.
Canonical Structure Z_eqType := Eval hnf in EqType Z Z_eqMixin.
Canonical Structure Z_choiceType := Eval hnf in ChoiceType Z Z_choiceMixin.
Canonical Structure Z_countType := Eval hnf in CountType Z Z_countMixin.

Definition betweenb x y z := (x <=? z) && (z <? y).

Lemma betweenbP x y z : reflect (x <= y < z) (betweenb x z y).
Proof. by apply/(iffP andP); case=> /Z.leb_spec0 H1 /Z.ltb_spec0 H2. Qed.

(* First we prove that Z/pZ forms a [ZmodType]. We only need that p > 0 for
 * this. Then, we prove that Z/pZ forms a [RingType], which in mathcomp cannot
 * be the trivial ring. Hence, we assume p > 1. Finally, we show that Z/pZ forms
 * a finite field, and consequently we assume that p is prime.
 *
 * We could use Coq's [Section]s to nicely divide the theory into pieces using
 * only the minimal hypothesis. However, this makes it hard for Coq to infer
 * canonical structures. We could pack the proofs of these hypotheses along the
 * type. However, not all statements have proof irrelevance, complicating
 * matters again.
 *
 * Hence, we choose the simplest solution: just develop this theory for this
 * specific [p]. Note that, besides the three facts [Hp_gt0], [Hp_gt1], and
 * [Hp_prime], we never look at the value of [p] itself. We enforce this through
 * locking [p]. *)

Definition p := locked (2^255 - 19).

Fact Hp_gt0 : p > 0.
Proof. by unlock p; rewrite Z.gt_lt_iff; apply/Z.ltb_spec0. Qed.
(* Faster proof:
unlock p.
rewrite Z.gt_lt_iff Z.lt_0_sub.
apply: (@Z.lt_trans _ (2^5)); first by apply/Z.ltb_spec0.
by apply: Z.pow_lt_mono_r; do [apply/Z.ltb_spec0 | apply/Z.leb_spec0].
*)

Lemma Hp_neq0 : p <> 0.
Proof. move: Hp_gt0=> ?; omega. Qed.

Module Zmodp.

Inductive type := Zmodp x of betweenb 0 p x.

Lemma Z_mod_betweenb x y : y > 0 -> betweenb 0 y (x mod y).
Proof. by move=> H; apply/betweenbP; apply: Z_mod_lt. Qed.

Definition pi (x : Z) : type := Zmodp (Z_mod_betweenb x Hp_gt0).
Coercion repr (x : type) : Z := let: @Zmodp x _ := x in x.

Definition zero : type := pi 0.
Definition one : type := pi 1.
Definition opp (x : type) : type := pi (p - x).
Definition add (x y : type) : type := pi (x + y).
Definition mul (x y : type) : type := pi (x * y).

End Zmodp.
Import Zmodp.

Canonical Structure Zmodp_subType := [subType for repr].
Definition Zmodp_eqMixin := Eval hnf in [eqMixin of type by <:].
Canonical Structure Zmodp_eqType := Eval hnf in EqType type Zmodp_eqMixin.
Definition Zmodp_choiceMixin := Eval hnf in [choiceMixin of type by <:].
Canonical Structure Zmodp_choiceType :=
  Eval hnf in ChoiceType type Zmodp_choiceMixin.
Definition Zmodp_countMixin := Eval hnf in [countMixin of type by <:].
Canonical Structure Zmodp_countType :=
  Eval hnf in CountType type Zmodp_countMixin.

Lemma modZp (x : type) : x mod p = x.
Proof. by apply: Zmod_small; apply/betweenbP; case: x. Qed.

Lemma reprK (x : type) : pi x = x.
Proof. by apply: val_inj; apply: modZp. Qed.

Lemma piK (x : Z) : betweenb 0 p x -> repr (pi x) = x.
Proof. by move/betweenbP=> Hx /=; apply: Zmod_small. Qed.

Module Zmodp_zmod.

Lemma add_assoc : associative add.
Proof.
move=> x y z; apply: val_inj.
by rewrite /= Zplus_mod_idemp_r Zplus_mod_idemp_l Zplus_assoc.
Qed.

Lemma add_comm : commutative add.
Proof. by move=> x y; apply: val_inj; rewrite /= Zplus_comm. Qed.

Lemma add_left_id : left_id zero add.
Proof. exact: reprK. Qed.

Lemma add_left_inv : left_inverse zero opp add.
Proof.
move=> x; apply: val_inj.
rewrite /= Zplus_mod_idemp_l Z.sub_add Z_mod_same; first by [].
exact: Hp_gt0.
Qed.

Module Exports.
Definition Zmodp_zmodMixin :=
  ZmodMixin add_assoc add_comm add_left_id add_left_inv.
Canonical Structure Zmodp_zmodType :=
  Eval hnf in ZmodType type Zmodp_zmodMixin.
End Exports.

End Zmodp_zmod.
Import Zmodp_zmod.Exports.

Lemma Zmodp_addE x y : (pi x + pi y)%R = pi (x + y).
Proof.
apply/eqP; rewrite eqE; apply/eqP=> /=.
by apply: esym; apply: Z.add_mod; apply: Hp_neq0.
Qed.

Fact Hp_gt1 : p > 1.
Proof. by unlock p; rewrite Z.gt_lt_iff; apply/Z.ltb_spec0. Qed.

Module Zmodp_ring.

Lemma mul_assoc : associative mul.
Proof.
move=> x y z; apply: val_inj.
by rewrite /= Zmult_mod_idemp_r Zmult_mod_idemp_l Zmult_assoc.
Qed.

Lemma mul_comm : commutative mul.
Proof. by move=> x y; apply: val_inj; rewrite /= Zmult_comm. Qed.

Lemma mul_left_id : left_id one mul.
Proof.
move=> x; apply: val_inj. rewrite /=.
rewrite Z.mod_1_l; last exact: Z.gt_lt Hp_gt1.
by rewrite Z.mul_1_l; apply: modZp.
Qed.

Lemma mul_left_distr : left_distributive mul add.
Proof.
move=> x y z; apply: val_inj.
rewrite /= Zmult_mod_idemp_l Zplus_mod_idemp_l Zplus_mod_idemp_r.
by rewrite Z.mul_add_distr_r.
Qed.

Lemma one_neq_zero : one != zero.
Proof.
rewrite -(eqtype.inj_eq val_inj) /=.
by rewrite Zmod_0_l Zmod_1_l; last exact: Z.gt_lt Hp_gt1.
Qed.

Module Exports.
Definition Zmodp_ringMixin := Eval hnf in
  ComRingMixin mul_assoc mul_comm mul_left_id mul_left_distr one_neq_zero.
Canonical Structure Zmodp_ringType := Eval hnf in RingType type Zmodp_ringMixin.
Canonical Structure Zmodp_comRingType := Eval hnf in ComRingType type mul_comm.
End Exports.

End Zmodp_ring.
Import Zmodp_ring.Exports.

Lemma Zmodp_mulE x y : (pi x * pi y)%R = pi (x * y).
Proof.
apply/eqP; rewrite eqE; apply/eqP=> /=.
by apply: esym; apply: Z.mul_mod; apply: Hp_neq0.
Qed.

Fact Hp_prime : prime p.
Proof. by unlock p; apply: primo. Qed.

Inductive Zinv_spec (x : Z) : Set :=
| Zinv_spec_zero : x mod p = 0 -> Zinv_spec x
| Zinv_spec_unit : x mod p <> 0 -> forall y, (y * x) mod p = 1 -> Zinv_spec x.

(* TODO: I don't like the use of the opaque [euclid]. *)
Lemma Zinv x : Zinv_spec x.
Proof.
case: (Z.eqb_spec (x mod p) 0); first exact: Zinv_spec_zero.
move=> Hx.
have [u v d Euv Hgcd]: Euclid (x mod p) p by apply: euclid.
wlog: u v d Euv Hgcd / (0 <= d) => [|Hd].
  case: (Z.leb_spec0 0 d) => Hd; first by apply; first exact: Euv.
  apply Z.nle_gt in Hd.
  have Hd2 : 0 <= -d by omega.
  have Hgcd2 : Zis_gcd (x mod p) p (-d)
    by apply: Zis_gcd_opp; apply: Zis_gcd_sym.
  apply; [| exact: Hgcd2 | exact: Hd2].
  rewrite -Euv Z.opp_add_distr -!Z.mul_opp_l.
  by congr (_ + _).
apply: (@Zinv_spec_unit _ Hx u).
rewrite -Z.mul_mod_idemp_r; last exact: Hp_neq0.
apply: Zdivide_mod_minus; first by move: Hp_gt1=> ?; omega.
rewrite /Z.divide; exists (-v).
rewrite Z.mul_opp_l -Z.add_move_0_r -Z.add_sub_swap Z.sub_move_0_r Euv.
rewrite -(Zis_gcd_gcd _ _ _ _ Hgcd); last exact: Hd.
rewrite Zgcd_1_rel_prime.
apply: rel_prime_le_prime; first exact: Hp_prime.
suff: 0 <= x mod p < p
  by move=> ?; omega.
by apply: Z.mod_pos_bound; apply: Z.gt_lt; apply: Hp_gt0.
Qed.

Definition Zmodp_inv (x : type) : type :=
  match Zinv x with
  | Zinv_spec_zero _ => zero
  | @Zinv_spec_unit _ _ y _ => pi y
  end.

Lemma modZp0 (x : type) : x mod p = 0 -> x == 0%R.
Proof. by rewrite modZp => Hx_eq0; rewrite -[x]reprK Hx_eq0. Qed.

Module Zmodp_field.

Lemma mulVx : GRing.Field.axiom Zmodp_inv.
Proof.
move=> x Hx_neq0.
rewrite /Zmodp_inv; case: (Zinv x); first by move/modZp0/eqP; move/eqP: Hx_neq0.
move=> Hxmodp_neq0 y Exy.
apply/eqP; rewrite eqE; apply/eqP=> /=.
rewrite Z.mul_mod_idemp_l; last exact: Hp_neq0.
by rewrite [1 mod p]Z.mod_small; last by move: Hp_gt1=> ?; omega.
Qed.

Lemma inv0 : Zmodp_inv 0%R = 0%R.
Proof.
rewrite /Zmodp_inv; case: (Zinv 0); first done.
have : 0 mod p = 0 by apply: Z.mod_0_l; exact: Hp_neq0.
done.
Qed.

Module Exports.
Definition Zmodp_unitRingMixin := Eval hnf in FieldUnitMixin mulVx inv0.
Canonical Structure Zmodp_unitRingType :=
  Eval hnf in UnitRingType type Zmodp_unitRingMixin.
Canonical Structure Zmodp_comUnitRingType :=
  Eval hnf in [comUnitRingType of type].

Lemma Zmodp_fieldMixin : GRing.Field.mixin_of Zmodp_unitRingType.
Proof. by move=> x Hx_neq0; rewrite qualifE /=. Qed.

Definition Zmodp_idomainMixin := FieldIdomainMixin Zmodp_fieldMixin.
Canonical Structure Zmodp_idomainType :=
  Eval hnf in IdomainType type Zmodp_idomainMixin.
Canonical Structure Zmodp_fieldType :=
  Eval hnf in FieldType type Zmodp_fieldMixin.
End Exports.

End Zmodp_field.

(* Useful tactic to compute boolean equalities. *)
Ltac zmodp_compute := rewrite ?(Zmodp_addE, Zmodp_mulE) eqE /=; unlock p=> /=.

Export Zmodp_zmod.Exports Zmodp_ring.Exports Zmodp_field.Exports.
