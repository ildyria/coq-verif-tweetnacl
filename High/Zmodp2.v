Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg finfield prime.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import curve25519_prime Zmodp prime_ssrprime.
From mathcomp Require Import galois.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope Z.
Open Scope ring_scope.
Import GRing.Theory.

Import Zmodp.

Module Zmodp2.

(* Lemma prime_p : prime.prime (Z.to_nat p).
Proof. apply prime_ssrprime. rewrite Z_of_nat_to_nat_p /p -lock; apply primo. Qed.

Lemma pow2_pos : is_true (leq (S O) (S (S O))).
Proof. done. Qed.

Check sval.
Definition GFp2 := sval (PrimePowerField prime_p pow2_pos).
*)

Inductive type := Zmodp2 (x: Zmodp.type) (y:Zmodp.type).

Definition pi (x : Zmodp.type * Zmodp.type) : type := Zmodp2 x.1 x.2.
Definition piZ (x : Z * Z) : type := Zmodp2 (Zmodp (Z_mod_betweenb x.1 Hp_gt0)) (Zmodp (Z_mod_betweenb x.2 Hp_gt0)).
Coercion repr (x : type) : Zmodp.type*Zmodp.type := let: Zmodp2 u v := x in (u, v).
Coercion reprZ (x : type) : Z*Z := let: Zmodp2 (@Zmodp u _) (@Zmodp v _) := x in (u, v).

Definition zero : type := pi (Zmodp.zero, Zmodp.zero).
Definition one : type := pi (Zmodp.one, Zmodp.zero).
Definition opp (x : type) : type := pi (Zmodp.opp x.1 , Zmodp.opp x.2).
Definition add (x y : type) : type := pi (x.1 + y.1, x.2 + y.2).
Definition mul (x y : type) : type := pi (x.1 * y.1 - x.2 * y.2 , x.1 * y.2 + x.2 * y.1).

Lemma pi_of_reprK : cancel repr pi.
Proof. by case. Qed.

End Zmodp2.

Import Zmodp2.


Definition Zmodp2_eqMixin := CanEqMixin pi_of_reprK.
Canonical Structure Zmodp2_eqType := Eval hnf in EqType type Zmodp2_eqMixin.
Definition Zmodp2_choiceMixin := CanChoiceMixin pi_of_reprK.
Canonical Structure Zmodp2_choiceType := Eval hnf in ChoiceType type Zmodp2_choiceMixin.
Definition Zmodp2_countMixin := CanCountMixin pi_of_reprK.
Canonical Structure Zmodp2_countType := Eval hnf in CountType type Zmodp2_countMixin.
Definition Zmodp2_finMixin := CanFinMixin pi_of_reprK.
Canonical Structure Zmodp2_finType := Eval hnf in FinType type Zmodp2_finMixin.

Lemma modZp_1 (x : type) : (Zmodp.repr x.1) mod p = (Zmodp.repr x.1).
Proof. by elim x.1 => xi i; apply: Zmod_small ; apply/betweenbP; move: i; case xi. Qed.

Lemma modZp_2 (x : type) : (Zmodp.repr x.2) mod p = (Zmodp.repr x.2).
Proof. by elim x.2 => xi i; apply: Zmod_small ; apply/betweenbP; move: i; case xi. Qed.

Lemma reprK (x : type) : pi x = x.
Proof. by case x. Qed.
Lemma piK (x : Zmodp.type*Zmodp.type) : repr (pi x) = x.
Proof. by case x. Qed.

Lemma piZK (x : Z*Z) : betweenb 0 p x.1 -> betweenb 0 p x.2 -> reprZ (piZ x) = x.
Proof. by case x => u v /= ; move/betweenbP => Hu /betweenbP => Hv /= ; f_equal; apply: Zmod_small. Qed.



Module Zmodp2_zmod.

Lemma add_assoc : associative add.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2] ; rewrite /add /= ; f_equal; f_equal; apply Zmodp_zmod.add_assoc.
Qed.

Lemma add_comm : commutative add.
Proof.
move=> [x1 x2] [y1 y2] ; rewrite /add /= ; f_equal; f_equal; apply Zmodp_zmod.add_comm.
Qed.

Lemma add_left_id : left_id zero add.
Proof. move => [x1 x2]. rewrite /add /=.
have ->: Zmodp.zero + x1 = x1.
  by apply Zmodp_zmod.add_left_id.
have ->: Zmodp.zero + x2 = x2.
  by apply Zmodp_zmod.add_left_id.
reflexivity.
Qed.

Lemma add_left_inv : left_inverse zero opp add.
Proof. move => [x1 x2]. rewrite /add /=.
have ->: Zmodp.opp x1 + x1 = 0.
  by apply Zmodp_zmod.add_left_inv.
have ->: Zmodp.opp x2 + x2 = 0.
  by apply Zmodp_zmod.add_left_inv.
reflexivity.
Qed.

Module Exports.
Definition Zmodp_zmodMixin :=
  ZmodMixin add_assoc add_comm add_left_id add_left_inv.
Canonical Structure Zmodp_zmodType :=
  Eval hnf in ZmodType type Zmodp_zmodMixin.
End Exports.

End Zmodp2_zmod.
Import Zmodp2_zmod.Exports.

Lemma Zmodp2_addE x y : (pi x + pi y)%R = pi (x + y).
Proof. reflexivity. Qed.

Lemma Zmodp_oppE x : (-pi x)%R = pi (-x).
Proof. reflexivity. Qed.

Fact Hp_gt1 : p > 1.
Proof. by unlock p; rewrite Z.gt_lt_iff; apply/Z.ltb_spec0. Qed.

Module Zmodp2_ring.

Lemma mul_comm : commutative mul.
Proof. move=> [x1 x2] [y1 y2] ; rewrite /mul /=.
have Hab: forall a b:Zmodp.type, a + b = b + a.
  by apply Zmodp_zmod.add_comm.
rewrite (Hab (y1 * x2) _ ).
f_equal ; f_equal ; f_equal; [|f_equal| | ];
apply Zmodp_ring.mul_comm.
Qed.


Lemma mul_assoc : associative mul.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2] ; rewrite /mul /= . f_equal.
f_equal ; apply val_inj => /=.
+ rewrite Zminus_mod_idemp_r.
  rewrite -(Zplus_mod (y1 * z1)).
  rewrite Zmult_mod_idemp_r.
  rewrite -(Zplus_mod (y1 * z2)).
  rewrite Zmult_mod_idemp_r.
  rewrite Zminus_mod_idemp_r.
  rewrite -Zplus_mod.
  rewrite Zminus_mod_idemp_r.
  rewrite -(Zplus_mod (x1 * y1)).
  rewrite Zmult_mod_idemp_l.
  rewrite -(Zplus_mod (x1 * y2)).
  rewrite Zmult_mod_idemp_l.
  rewrite Zminus_mod_idemp_r.
  rewrite -Zplus_mod.
  have ->: (x1 * (y1 * z1 + (p - y2 * z2)) + (p - x2 * (y1 * z2 + y2 * z1)) = 
            x1 * (y1 * z1 + (- y2 * z2)) + (- x2 * (y1 * z2 + y2 * z1)) + (x1 + 1) * p)%Z by ring.
  have ->: ((x1 * y1 + (p - x2 * y2)) * z1 + (p - (x1 * y2 + x2 * y1) * z2) = 
            x1 * (y1 * z1 + (- y2 * z2)) + (- x2 * (y1 * z2 + y2 * z1)) + (z1 + 1) * p)%Z by ring.
  by rewrite ?Z_mod_plus_full.
+ rewrite Zminus_mod_idemp_r.
  rewrite -(Zplus_mod (y1 * z2)).
  rewrite Zmult_mod_idemp_r.
  rewrite -(Zplus_mod (y1 * z1)).
  rewrite Zmult_mod_idemp_r.
  rewrite -Zplus_mod.
  rewrite Zminus_mod_idemp_r.
  rewrite -(Zplus_mod (x1 * y1)).
  rewrite Zmult_mod_idemp_l.
  rewrite -(Zplus_mod (x1 * y2)).
  rewrite Zmult_mod_idemp_l.
  rewrite -Zplus_mod.
  have ->: (x1 * (y1 * z2 + y2 * z1) + x2 * (y1 * z1 + (p - y2 * z2)) = 
            x1 * (y1 * z2 + y2 * z1) + x2 * (y1 * z1 + ( - y2 * z2)) + (x2 * p))%Z by ring.
  have ->: ((x1 * y1 + (p - x2 * y2)) * z2 + (x1 * y2 + x2 * y1) * z1 = 
            x1 * (y1 * z2 + y2 * z1) + x2 * (y1 * z1 + ( - y2 * z2)) + (z2 * p))%Z by ring.
  by rewrite ?Z_mod_plus_full.
Qed.

Lemma mul_left_id : left_id one mul.
Proof.
move=> [x1 x2]. rewrite /mul /=.
have ->: Zmodp.one * x1 = x1.
  by apply Zmodp_ring.mul_left_id.
have ->: Zmodp.one * x2 = x2.
  by apply Zmodp_ring.mul_left_id.
have ->: Zmodp.zero * x2 = Zmodp.zero.
  reflexivity.
have ->: Zmodp.zero * x1 = Zmodp.zero.
  reflexivity.
have ->: -Zmodp.zero = Zmodp.zero.
  apply val_inj => /=.
  rewrite Zminus_mod_idemp_r.
  rewrite -Zminus_mod_idemp_l.
  rewrite Z_mod_same_full.
  reflexivity.
  have ->: x1 + Zmodp.zero = Zmodp.zero + x1.
    apply val_inj => /=.
    rewrite Zmod_0_l.
    rewrite Z.add_0_r.
    reflexivity.
  have ->: x2 + Zmodp.zero = Zmodp.zero + x2.
    apply val_inj => /=.
    rewrite Zmod_0_l.
    rewrite Z.add_0_r.
    reflexivity.
  have ->: Zmodp.zero + x1 = x1.
    by apply Zmodp_zmod.add_left_id.
  have ->: Zmodp.zero + x2 = x2.
    by apply Zmodp_zmod.add_left_id.
  reflexivity.
Qed.

Lemma mul_left_distr : left_distributive mul add.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2]. rewrite /mul /add /=. f_equal.
f_equal; apply val_inj => /=.
+ rewrite Zmult_mod_idemp_l.
  rewrite Zmult_mod_idemp_l.
  rewrite Zminus_mod_idemp_r.
  rewrite -Zplus_mod.
  rewrite Zminus_mod_idemp_r.
  rewrite Zminus_mod_idemp_r.
  rewrite -(Zplus_mod (x1 * z1)).
  rewrite -(Zplus_mod (y1 * z1)).
  rewrite -Zplus_mod.
  have ->: ((x1 + y1) * z1 + (p - (x2 + y2) * z2) = 
          (x1 + y1) * z1 + - (x2 + y2) * z2 + 1 * p)%Z by ring.
  have ->: (x1 * z1 + (p - x2 * z2) + (y1 * z1 + (p - y2 * z2)) = 
          (x1 + y1) * z1 + - (x2 + y2) * z2 + 2 * p)%Z by ring.
  by rewrite ?Z_mod_plus_full.
+ rewrite Zmult_mod_idemp_l.
  rewrite Zmult_mod_idemp_l.
  rewrite -Zplus_mod.
  rewrite -(Zplus_mod (x1 * z2)).
  rewrite -(Zplus_mod (y1 * z2)).
  rewrite -Zplus_mod.
  f_equal.
  ring.
Qed.

Lemma one_neq_zero : one != zero.
Proof.
rewrite /one /zero; f_equal.
apply/eqP => H ; inversion H; move: H1.
by rewrite Zmod_0_l Zmod_1_l; last exact: Z.gt_lt Hp_gt1.
Qed.

Module Exports.
Definition Zmodp_ringMixin := Eval hnf in ComRingMixin mul_assoc mul_comm mul_left_id mul_left_distr one_neq_zero.
Canonical Structure Zmodp_ringType := Eval hnf in RingType type Zmodp_ringMixin.
Canonical Structure Zmodp_comRingType := Eval hnf in ComRingType type mul_comm.
End Exports.

End Zmodp2_ring.
Import Zmodp2_ring.Exports.

Lemma Zmodp_mulE x y : (pi x * pi y)%R = pi (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1).
Proof.
apply/eqP; rewrite eqE; apply/eqP=> /=.
reflexivity.
(* apply: esym. f_equal; apply val_inj => /=.
apply: Z.mul_mod.
apply val_inj.
by apply: esym; apply: Z.mul_mod; apply: Hp_neq0.
 *)Qed.

Fact Hp_prime : prime p.
Proof. by unlock p; apply: primo. Qed.

(* Inductive Zinv_spec (x : Z) : Set :=
| Zinv_spec_zero : x = zero -> Zinv_spec x
| Zinv_spec_unit : x mod p <> 0 -> forall y, (y * x) mod p = 1 -> Zinv_spec x.
 *)
(* TODO: I don't like the use of the opaque [euclid]. *)
(* Lemma Zinv x : Zinv_spec x.
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
Qed. *)(* 

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
Export Zmodp_field.Exports. *)
