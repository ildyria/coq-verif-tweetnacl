Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
Require Import ZArith.
From Tweetnacl.High Require Import Zmodp Zmodp_Ring GRing_tools.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope Z.
Import Zmodp.
Open Scope ring_scope.
Import GRing.Theory.

Module Zmodp2.

Inductive type := Zmodp2 (x: Zmodp.type) (y:Zmodp.type).

Definition pi (x : Zmodp.type * Zmodp.type) : type := Zmodp2 x.1 x.2.
Coercion repr (x : type) : Zmodp.type*Zmodp.type := let: Zmodp2 u v := x in (u, v).

Definition zero : type := pi (0%:R, 0%:R).
Definition one : type := pi (1, 0%:R).
Definition opp (x : type) : type := pi (- x.1 , - x.2).
Definition add (x y : type) : type := pi (x.1 + y.1, x.2 + y.2).
Definition sub (x y : type) : type := pi (x.1 - y.1, x.2 - y.2).
Definition mul (x y : type) : type := pi ((x.1 * y.1) + (2%:R * (x.2 * y.2)), (x.1 * y.2) + (x.2 * y.1)).

Lemma pi_of_reprK : cancel repr pi.
Proof. by case. Qed.

Definition eqb (x y : type) := match x, y with
  | Zmodp2 x1 x2, Zmodp2 y1 y2 => Zmodp.eqb x1 y1 && Zmodp.eqb x2 y2
end.

Lemma eqb_spec (x y: type) : reflect (x = y) (eqb x y).
Proof.
apply Bool.iff_reflect.
split.
+ move => ->.
  rewrite /eqb.
  case y => y1 y2.
  by apply/andP ; split ; apply /Refl.eqb_spec.
+ rewrite /eqb.
  case x => x1 x2.
  case y => y1 y2.
  by move/andP => [] /Refl.eqb_spec -> /Refl.eqb_spec ->.
Qed.

Lemma Zmodp2_inv : forall a b c d, Zmodp2 a c = Zmodp2 b d -> a = b /\ c = d.
Proof. by move => a b c d H; inversion H. Qed.

Ltac Zmodp2_unfold := rewrite /mul /sub /add /opp /zero /one.

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

Lemma Zmodp2_const x1 x2 y1 y2: x1 = y1 -> x2 = y2 -> Zmodp2 x1 x2 = Zmodp2 y1 y2.
Proof. move=> -> -> //. Qed.

Local Ltac solve_this :=
  repeat match goal with
    | _ => progress Zmodp2_unfold; ring_unfold
    | [ |- context[Zmodp2 ?A ?B]] => have ->: Zmodp2 A B = Zmodp2.pi (A,B) => //
    | _ => solve[f_equal ; f_equal ; ring]
    | _ => solve[f_equal ; f_equal ; Zmodp_ringify ; ring_simplify_this]
  end.

Module Zmodp2_zmod.

Lemma add_comm : commutative add.
Proof.
move=> [x1 x2] [y1 y2].
solve_this.
Qed.

Lemma add_left_id : left_id zero add.
Proof. move => [x1 x2].
solve_this.
Qed.

Lemma add_left_inv : left_inverse zero opp add.
Proof. move => [x1 x2].
solve_this.
rewrite Zmodp_zmod.add_left_inv.
rewrite Zmodp_zmod.add_left_inv.
reflexivity.
Qed.

Lemma add_assoc : associative add.
Proof. move=> [x1 x2] [y1 y2] [z1 z2].
solve_this.
Qed.

Lemma add_sub : forall (x y:type), sub x y = add x (opp y).
Proof.
move=> x y.
solve_this.
Qed.

Module Exports.
Definition Zmodp_zmodMixin :=
  ZmodMixin add_assoc add_comm add_left_id add_left_inv.
Canonical Structure Zmodp_zmodType :=
  Eval hnf in ZmodType type Zmodp_zmodMixin.
End Exports.

End Zmodp2_zmod.
Import Zmodp2_zmod.Exports.

Lemma Zmodp2_addE x y : (pi x + pi y)%R = pi (x.1 + y.1, x.2 + y.2).
Proof. reflexivity. Qed.

Lemma Zmodp2_oppE x : (-pi x)%R = pi (-x).
Proof. reflexivity. Qed.

Fact Hp_gt1 : p > 1.
Proof. by unlock p; rewrite Z.gt_lt_iff; apply/Z.ltb_spec0. Qed.

Module Zmodp2_ring.

Lemma mul_comm : commutative mul.
Proof. move=> [x1 x2] [y1 y2].
solve_this.
Qed.

Lemma mul_assoc : associative mul.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2].
solve_this.

Qed.

Lemma mul_left_id : left_id one mul.
Proof.
move=> [x1 x2].
solve_this.
Qed.

Lemma mul_left_distr : left_distributive mul add.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2].
solve_this.
Qed.

Lemma one_neq_zero : one != zero.
Proof.
rewrite /one /zero; f_equal.
apply/eqP => H ; inversion H; move: H1.
by rewrite Zmod_0_l Zmod_1_l; last exact: Z.gt_lt Hp_gt1.
Qed.

Lemma two_neq_zero : (one + one) != zero.
Proof.
rewrite /one /zero; f_equal.
zmodp_compute.
apply/eqP => H ; inversion H; clear H; move: H1.
rewrite /p -lock.
by compute.
Qed.

Lemma three_neq_zero : (one + one + one) != zero.
Proof.
rewrite /one /zero; f_equal.
zmodp_compute.
apply/eqP => H ; inversion H; clear H; move: H1.
rewrite /p -lock.
by compute.
Qed.


Module Exports.
Definition Zmodp2_ringMixin := Eval hnf in ComRingMixin mul_assoc mul_comm mul_left_id mul_left_distr one_neq_zero.
Canonical Structure Zmodp2_ringType := Eval hnf in RingType type Zmodp2_ringMixin.
Canonical Structure Zmodp2_comRingType := Eval hnf in ComRingType type mul_comm.
End Exports.

End Zmodp2_ring.
Import Zmodp2_ring.Exports.

Lemma Zmodp2_mulE x y : (pi x * pi y)%R = pi (x.1 * y.1 + (Zmodp.pi 2) * (x.2 * y.2), x.1 * y.2 + x.2 * y.1).
Proof.
apply/eqP; rewrite pi_2 eqE; apply/eqP=> //=.
Qed.

Inductive Zinv_spec (x : type) : Type :=
| Zinv_spec_zero : x = zero -> Zinv_spec x
| Zinv_spec_unit : x <> zero -> forall y, (y * x)%R = one -> Zinv_spec x.

Lemma Zinv x : Zinv_spec x.
Proof.
case_eq (eqb x zero) ; move/eqb_spec.
+ move => -> ; exact: Zinv_spec_zero.
+ destruct x as [x y] => Hxy.
apply (@Zinv_spec_unit (Zmodp2 x y) Hxy (Zmodp2 (x/(x^+2-2%:R*y^+2)) (-y/(x^+2-2%:R*y^+2)))).
rewrite /GRing.mul /= /mul /=.
Zmodp_ringify.
have ->: x / (x ^+ 2 - 2%:R * y ^+ 2) * x + 2%:R * (- y / (x ^+ 2 - 2%:R * y ^+ 2) * y) = (x ^+2 - 2%:R * y^+2) / (x ^+ 2 - 2%:R * y ^+ 2).
remember (x ^+ 2 - 2%:R * y ^+ 2) as M.
by rewrite (mulrC x) (mulrC (-y)) ?mulrA (mulrC (2%:R)) -?mulrA -mulrDr mulrC mulNr mulrN HeqM ?expr2.
have ->: x / (x ^+ 2 - 2%:R * y ^+ 2) * y + - y / (x ^+ 2 - 2%:R * y ^+ 2) * x = 0.
remember (x ^+ 2 - 2%:R * y ^+ 2) as M.
by rewrite (mulrC x) (mulrC (-y)) -?mulrA (mulrC x) mulNr mulrN addrN.
rewrite mulfV //.
apply x2_eq_2_y2.
apply/orP.
move/eqP: Hxy.
apply/contraR.
case_eq (x != 0) ; move/eqP;
case_eq (y != 0) ; move/eqP => //= => -> -> _.
apply/eqP => //=.
Qed.

Definition Zmodp2_inv (x : type) : type :=
  match Zinv x with
  | Zinv_spec_zero _ => zero
  | @Zinv_spec_unit _ _ y _ => pi y
  end.

Module Zmodp2_field.

Lemma mulVx : GRing.Field.axiom Zmodp2_inv.
Proof.
move=> x Hx_neq0.
rewrite /Zmodp2_inv.
case: (Zinv x).
+ by move/eqP: Hx_neq0.
+ move=> Hxx_neq0 y.
done.
Qed.

Lemma inv0 : Zmodp2_inv 0%R = 0%R.
Proof.
rewrite /Zmodp2_inv; case: (Zinv 0); done.
Qed.

Module Exports.
Definition Zmodp2_unitRingMixin := Eval hnf in FieldUnitMixin mulVx inv0.
Canonical Structure Zmodp2_unitRingType :=
  Eval hnf in UnitRingType type Zmodp2_unitRingMixin.
Canonical Structure Zmodp2_comUnitRingType :=
  Eval hnf in [comUnitRingType of type].

Lemma Zmodp2_fieldMixin : GRing.Field.mixin_of Zmodp2_unitRingType.
Proof. by move=> x Hx_neq0; rewrite qualifE /=. Qed.

Definition Zmodp2_idomainMixin := FieldIdomainMixin Zmodp2_fieldMixin.
Canonical Structure Zmodp2_idomainType :=
  Eval hnf in IdomainType type Zmodp2_idomainMixin.
Canonical Structure Zmodp2_fieldType :=
  Eval hnf in FieldType type Zmodp2_fieldMixin.
End Exports.

End Zmodp2_field.
Import Zmodp2_field.Exports.

(* Useful tactic to compute boolean equalities. *)
Ltac zmodp2_compute := rewrite ?(Zmodp2_addE, Zmodp2_mulE) eqE /=; unlock p=> /=.

(* Now create the finalg variants too. *)
Canonical Structure Zmodp2_finZmodType := Eval hnf in [finZmodType of type].
Canonical Structure Zmodp2_finRingType := Eval hnf in [finRingType of type].
Canonical Structure Zmodp2_finComRingType := Eval hnf in [finComRingType of type].
Canonical Structure Zmodp2_finUnitRingType := Eval hnf in [finUnitRingType of type].
Canonical Structure Zmodp2_finComUnitRingType := Eval hnf in [finComUnitRingType of type].
Canonical Structure Zmodp2_finIdomainType := Eval hnf in [finIdomainType of type].
Canonical Structure Zmodp2_finFieldType := Eval hnf in [finFieldType of type].

Export Zmodp2_zmod.Exports Zmodp2_ring.Exports.
Export Zmodp2_field.Exports.

Import GRing.Theory.

Lemma Zmodp2_ring : ring_theory zero one add mul sub opp eq.
Proof.
apply mk_rt.
apply Zmodp2_zmod.add_left_id.
apply Zmodp2_zmod.add_comm.
apply Zmodp2_zmod.add_assoc.
apply Zmodp2_ring.mul_left_id.
apply Zmodp2_ring.mul_comm.
apply Zmodp2_ring.mul_assoc.
apply Zmodp2_ring.mul_left_distr.
apply Zmodp2_zmod.add_sub.
move => x. rewrite Zmodp2_zmod.add_comm Zmodp2_zmod.add_left_inv //.
Defined.

Lemma Zmodp2_ring2 : @ring_theory (GRing.Ring.sort Zmodp2_ringType) Zmodp2.zero Zmodp2.one Zmodp2.add Zmodp2.mul Zmodp2.sub Zmodp2.opp eq.
Proof.
apply mk_rt.
apply Zmodp2_zmod.add_left_id.
apply Zmodp2_zmod.add_comm.
apply Zmodp2_zmod.add_assoc.
apply Zmodp2_ring.mul_left_id.
apply Zmodp2_ring.mul_comm.
apply Zmodp2_ring.mul_assoc.
apply Zmodp2_ring.mul_left_distr.
apply Zmodp2_zmod.add_sub.
move => x. rewrite Zmodp2_zmod.add_comm Zmodp2_zmod.add_left_inv //.
Defined.

Add Ring Zmodp2_ring : Zmodp2_ring.
Add Ring Zmodp2_ring2 : Zmodp2_ring2.

Open Scope ring_scope.

Ltac Zmodp2_ringify := repeat match goal with
  | [ |- context[Zmodp2.mul ?a ?b]] => have ->: (Zmodp2.mul a b) = a * b => //
  | [ |- context[Zmodp2.add ?a (Zmodp2.opp ?b)]] => have ->: (Zmodp2.add a (Zmodp2.opp b)) = a - b => //
  | [ |- context[Zmodp2.opp ?a]] => have ->: Zmodp2.opp a = -a => //
  | [ |- context[Zmodp2.add ?a ?b]] => have ->: (Zmodp2.add a b) = a + b => //
  | [ |- context[Zmodp2.one] ] => have ->: Zmodp2.one = 1 => //
  | [ |- context[Zmodp2.zero] ] => have ->: Zmodp2.zero = 0 => //
  end.

Close Scope ring_scope.