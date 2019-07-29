Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import prime_cert.

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

Lemma Hp_neq0 : p <> 0.
Proof. move: Hp_gt0=> ?; omega. Qed.

Module Zmodp.

Inductive type := Zmodp x of betweenb 0 p x.

Lemma Z_mod_betweenb x y : y > 0 -> betweenb 0 y (x mod y).
Proof. by move=> H; apply/betweenbP; apply: Z_mod_lt. Defined.

Definition pi (x : Z) : type := Zmodp (Z_mod_betweenb x Hp_gt0).
Coercion repr (x : type) : Z := let: @Zmodp x _ := x in x.

Definition zero : type := pi 0.
Definition one : type := pi 1.
Definition opp (x : type) : type := pi (p - x).
Definition add (x y : type) : type := pi (x + y).
Definition sub (x y : type) : type := pi (x - y).
Definition mul (x y : type) : type := pi (x * y).

Definition eqb x y := match x, y with
  | Zmodp x _ , Zmodp y _ => Z.eqb x y
end.

Lemma Zeqb_eqb x y : Z.eqb x y -> eqb (pi x) (pi y).
Proof.
move/Z.eqb_spec ->.
rewrite /eqb.
case (pi y) => yi _.
apply Z.eqb_refl.
Qed.

Lemma Zeqb_eq x y : Z.eqb x y -> pi x = pi y.
Proof. by move/Z.eqb_spec ->. Qed.

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
Proof. apply: val_inj. apply: modZp. Qed.

Lemma piK (x : Z) : betweenb 0 p x -> repr (pi x) = x.
Proof. by move/betweenbP=> Hx /=; apply: Zmod_small. Qed.

(* Lemma x_eq_0 : forall x:Z,
0 <= x < p -> x <> 0 -> x mod p <> 0.
Proof.
move=> x Hx Hx' Hx''.
apply:Hx'.
move: Hx''.
rewrite Z.mod_divide; last by rewrite /p -lock.
move => Hx'.
rewrite -(Zmod_small x p Hx).
by apply Zdivide_mod.
Qed. *)

Module Zmodp_finite.

Definition pn := Z.to_nat p.
Lemma pn_to_p : Z.of_nat pn = p.
Proof. by rewrite Z2Nat.id //; move: Hp_gt0=> ?; omega. Qed.

Lemma ord_of_Zmodp_ok x : betweenb 0 p x -> (Z.to_nat x < pn)%nat.
Proof.
move/betweenbP=> [Hx1 Hx2].
by apply/ltP/Nat2Z.inj_lt; rewrite pn_to_p Z2Nat.id.
Qed.

Lemma Zmodp_of_ord_ok n : (n < pn)%nat -> betweenb 0 p (Z.of_nat n).
Proof.
move/ltP/Nat2Z.inj_lt; rewrite pn_to_p => H1.
have H2: 0 <= Z.of_nat n by apply: Nat2Z.is_nonneg.
by apply/betweenbP.
Qed.

Definition ord_of_Zmodp (x : type) : 'I_pn :=
  let: @Zmodp _ Hx := x in Ordinal (ord_of_Zmodp_ok Hx).

Definition Zmodp_of_ord (n : 'I_pn) : type :=
  let: @Ordinal _ _ Hn := n in Zmodp (Zmodp_of_ord_ok Hn).

Lemma ord_of_ZmodpK : cancel ord_of_Zmodp Zmodp_of_ord.
Proof.
move=> [x Hx] /=.
apply/eqP; rewrite eqE; apply/eqP=> /=.
by apply: Z2Nat.id; move/betweenbP: Hx=> [].
Qed.

Module Exports.
Definition Zmodp_finMixin := CanFinMixin ord_of_ZmodpK.
Canonical Structure Zmodp_finType := Eval hnf in FinType type Zmodp_finMixin.
Canonical Structure Zmodp_subFinType := Eval hnf in [subFinType of type].
End Exports.

End Zmodp_finite.
Import Zmodp_finite.Exports.

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

Lemma add_sub : forall (x y:type), sub x y = add x (opp y).
Proof.
move=> x y; apply: val_inj => /=.
have H:= Hp_neq0.
rewrite -(Zminus_mod_idemp_l p) Z.mod_same ?Zplus_mod_idemp_r //.
Qed.

Module Exports.
Definition Zmodp_zmodMixin :=
  ZmodMixin add_assoc add_comm add_left_id add_left_inv.
Canonical Structure Zmodp_zmodType :=
  Eval hnf in ZmodType type Zmodp_zmodMixin.
End Exports.

End Zmodp_zmod.
Import Zmodp_zmod.Exports.

Module Refl.

Lemma eqb_spec (x y: type) : reflect (x = y) (eqb x y).
Proof.
apply Bool.iff_reflect.
split.
+ move => ->.
  rewrite /eqb.
  case x => xi Hxi.
  case y => yi Hyi.
  by apply Z.eqb_refl.
+ 
move=> H.
rewrite -(reprK x).
rewrite -(reprK y).
move: H.
rewrite /eqb.
case x.
case y.
move=> xi Hxi yi Hyi /=.
by move/Zeqb_eq.
Qed.

End Refl.

Import Refl.

Lemma Zmodp_addE x y : (pi x + pi y)%R = pi (x + y).
Proof.
apply/eqP; rewrite eqE; apply/eqP=> /=.
by apply: esym; apply: Z.add_mod; apply: Hp_neq0.
Qed.

Lemma Zmodp_oppE x : (-pi x)%R = pi (-x).
Proof.
apply/eqP; rewrite eqE; apply/eqP=> /=.
move: Hp_neq0=> Hp_neq0. (* Intro to proof env so we can discharge this easy *)
case: (Z.eqb_spec (x mod p) 0) => Hx.
- by rewrite Hx Z.mod_opp_l_z // Z.sub_0_r Z.mod_same.
- by rewrite -Z.mod_opp_l_nz // Z.mod_mod.
Qed.

Fact Hp_gt1 : p > 1.
Proof. by unlock p; rewrite Z.gt_lt_iff; apply/Z.ltb_spec0. Qed.

Module Zmodp_ring.

Lemma mul_assoc : associative mul.
Proof.
move=> x y z. apply: val_inj.
by rewrite /= Zmult_mod_idemp_r Zmult_mod_idemp_l Zmult_assoc.
Qed.

Lemma mul_comm : commutative mul.
Proof. by move=> x y; apply: val_inj; rewrite /= Zmult_comm. Qed.

Lemma mul_left_id : left_id one mul.
Proof.
move=> x. apply: val_inj. rewrite /=.
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
  | @Zinv_spec_unit _ _ y _ => pi (Z.modulo y p)
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
have HP:= Hp_gt1.
rewrite ?Z.mul_mod_idemp_l; last exact: Hp_neq0.
by rewrite [1 mod p]Z.mod_small ; last by move: Hp_gt1=> ?; omega.
omega.
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
Import Zmodp_field.Exports.

(* Useful tactic to compute boolean equalities. *)
Ltac zmodp_compute := rewrite ?(Zmodp_addE, Zmodp_mulE) eqE /=; unlock p=> /=.

(* Now create the finalg variants too. *)
Canonical Structure Zmodp_finZmodType := Eval hnf in [finZmodType of type].
Canonical Structure Zmodp_finRingType := Eval hnf in [finRingType of type].
Canonical Structure Zmodp_finComRingType := Eval hnf in [finComRingType of type].
Canonical Structure Zmodp_finUnitRingType := Eval hnf in [finUnitRingType of type].
Canonical Structure Zmodp_finComUnitRingType := Eval hnf in [finComUnitRingType of type].
Canonical Structure Zmodp_finIdomainType := Eval hnf in [finIdomainType of type].
Canonical Structure Zmodp_finFieldType := Eval hnf in [finFieldType of type].

Export Zmodp_finite.Exports Zmodp_zmod.Exports Zmodp_ring.Exports.
Export Zmodp_field.Exports.

Import GRing.Theory.


Lemma Zmodp_ring : ring_theory zero one add mul sub opp eq.
Proof.
apply mk_rt.
apply Zmodp_zmod.add_left_id.
apply Zmodp_zmod.add_comm.
apply Zmodp_zmod.add_assoc.
apply Zmodp_ring.mul_left_id.
apply Zmodp_ring.mul_comm.
apply Zmodp_ring.mul_assoc.
apply Zmodp_ring.mul_left_distr.
apply Zmodp_zmod.add_sub.
move => x. rewrite Zmodp_zmod.add_comm Zmodp_zmod.add_left_inv //.
Defined.

Add Ring Zmodp_ring : Zmodp_ring.

Lemma eq_inv_2 : forall (x m:Zmodp.type), (m = (Zmodp.pi 28948022309329048855892746252171976963317496166410141009864396001978282409975%Z) * x)%R -> ((Zmodp.pi 2) * m = x)%R.
Proof.
move => m x ->.
apply val_inj => /=.
rewrite Z.mul_mod_idemp_l ; last apply Hp_neq0.
rewrite Z.mul_mod_idemp_l ; last apply Hp_neq0.
rewrite Z.mul_mod_idemp_r ; last apply Hp_neq0.
rewrite Z.mul_assoc.
rewrite -Z.mul_mod_idemp_l ; last apply Hp_neq0.
have ->: (2 * 28948022309329048855892746252171976963317496166410141009864396001978282409975) mod p = 1.
rewrite /p -lock //.
rewrite Z.mul_1_l.
apply modZp.
Qed.

Open Scope ring_scope.

Lemma pi_2 : Zmodp.pi 2 = 2%:R.
Proof. by apply/eqP ; zmodp_compute. Qed.

Lemma pi_3 : Zmodp.pi 3 = 3%:R.
Proof. by apply/eqP ; zmodp_compute. Qed.

Lemma add_eq_mul2: forall (x:Zmodp.type),
  2%:R * x = x + x.
Proof.
  move => x.
  have -> : 2%:R = 1%:R + 1%:R :> Zmodp.type by apply val_inj => //=.
  rewrite GRing.mulrDl GRing.mul1r //.
Qed.

Lemma time_2_eq_0 (a:Zmodp.type) : 2%:R * a = 0 ->  a = 0.
Proof.
  move/(f_equal (fun x => (2%:R^-1) * x)).
  rewrite GRing.mulrA GRing.mulr0 (mulrC 2%:R^-1) GRing.mulfV.
  rewrite GRing.mul1r //.
  by zmodp_compute.
Qed.

Lemma mult_xy_eq_0: forall (x y: Zmodp.type),
  x * y = 0 -> x = 0 \/ y = 0.
Proof. by move => x y/eqP; rewrite mulf_eq0 ; move/orP => []/eqP -> ; [left|right]. Qed.

Ltac Zmodp_ringify := repeat match goal with
  | [ |- context[Zmodp.pi 2]] => rewrite pi_2
  | [ |- context[Zmodp.pi 3]] => rewrite pi_3
  | [ |- context[Zmodp.mul ?a ?b]] => have ->: (Zmodp.mul a b) = a * b => //
  | [ |- context[Zmodp.add ?a (Zmodp.opp ?b)]] => have ->: (Zmodp.add a (Zmodp.opp b)) = a - b => //
  | [ |- context[Zmodp.opp ?a]] => have ->: Zmodp.opp a = -a => //
  | [ |- context[Zmodp.add ?a ?b]] => have ->: (Zmodp.add a b) = a + b => //
  | [ |- context[Zmodp.one] ] => have ->: Zmodp.one = 1 => //
  | [ |- context[Zmodp.zero] ] => have ->: Zmodp.zero = 0 => //
  end.


Close Scope ring_scope.
