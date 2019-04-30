Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg finfield prime.
Require Import ZArith ZArith.Znumtheory.
From Tweetnacl.High Require Import curve25519_prime Zmodp prime_ssrprime.
From mathcomp Require Import galois.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope Z.
Import Zmodp.
Open Scope ring_scope.
Import GRing.Theory.

Module Zmodp2.

Inductive type := Zmodp2 (x: Zmodp.type) (y:Zmodp.type).

Definition pi (x : Zmodp.type * Zmodp.type) : type := Zmodp2 x.1 x.2.
Definition piZ (x : Z * Z) : type := Zmodp2 (Zmodp (Z_mod_betweenb x.1 Hp_gt0)) (Zmodp (Z_mod_betweenb x.2 Hp_gt0)).
Coercion repr (x : type) : Zmodp.type*Zmodp.type := let: Zmodp2 u v := x in (u, v).
Coercion reprZ (x : type) : Z*Z := let: Zmodp2 (@Zmodp u _) (@Zmodp v _) := x in (u, v).

Definition zero : type := pi (Zmodp.zero, Zmodp.zero).
Definition one : type := pi (Zmodp.one, Zmodp.zero).
Definition opp (x : type) : type := pi (Zmodp.opp x.1 , Zmodp.opp x.2).
Definition add (x y : type) : type := pi (Zmodp.add x.1 y.1, Zmodp.add x.2 y.2).
Definition sub (x y : type) : type := pi (Zmodp.sub x.1 y.1, Zmodp.sub x.2 y.2).
Definition mul (x y : type) : type := pi (Zmodp.add (Zmodp.mul x.1 y.1) (Zmodp.mul (Zmodp.pi 2) (Zmodp.mul x.2 y.2)), Zmodp.add (Zmodp.mul x.1 y.2) (Zmodp.mul x.2 y.1)).

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

Lemma Zmodp2_const x1 x2 y1 y2: x1 = y1 -> x2 = y2 -> Zmodp2 x1 x2 = Zmodp2 y1 y2.
Proof. move=> -> -> //. Qed.

(* Lemma type_dec x : x = zero \/ x <> zero.
Proof.
case x => [x1 x2].
case_eq (Zmodp.eqb x1 Zmodp.zero); move/Refl.eqb_spec.
case_eq (Zmodp.eqb x2 Zmodp.zero); move/Refl.eqb_spec.
by move=> -> -> ; left => //.
by move=> Hx2 Hx1 ; right => H ; apply Hx2 ; inversion H.
by move=> Hx1 ; right => H ; apply Hx1 ; inversion H.
Qed. *)

Module Zmodp2_zmod.

Lemma add_comm : commutative add.
Proof.
move=> [x1 x2] [y1 y2] ; rewrite /add /= ; f_equal; f_equal ; ring.
Qed.

Lemma add_left_id : left_id zero add.
Proof. move => [x1 x2]. rewrite /add /=.
rewrite Zmodp_zmod.add_left_id.
rewrite Zmodp_zmod.add_left_id.
reflexivity.
Qed.

Lemma add_left_inv : left_inverse zero opp add.
Proof. move => [x1 x2]. rewrite /add /=.
rewrite Zmodp_zmod.add_left_inv.
rewrite Zmodp_zmod.add_left_inv.
reflexivity.
Qed.

Lemma add_assoc : associative add.
Proof. move=> [x1 x2] [y1 y2] [z1 z2] ; rewrite /add /= ; f_equal; f_equal; apply Zmodp_zmod.add_assoc. Qed.

Lemma add_sub : forall (x y:type), sub x y = add x (opp y).
Proof.
move=> x y.
rewrite /sub /add /opp.
f_equal; f_equal => /= ; ring.
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
Proof. move=> [x1 x2] [y1 y2] ; rewrite /mul /=.
f_equal; f_equal; ring.
Qed.

Lemma mul_assoc : associative mul.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2] ; rewrite /mul /= . f_equal.
f_equal.
+ ring.
+ ring.
(*  ; apply val_inj => /=.
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
  by rewrite ?Z_mod_plus_full. *)
Qed.

Lemma mul_left_id : left_id one mul.
Proof.
move=> [x1 x2]. rewrite /mul /=.
rewrite Zmodp_ring.mul_left_id.
rewrite Zmodp_ring.mul_left_id.
have ->: Zmodp.mul Zmodp.zero x2 = Zmodp.zero => //.
have ->: Zmodp.mul Zmodp.zero x1 = Zmodp.zero => //.
have ->: Zmodp.add x1 (Zmodp.mul (Zmodp.pi 2) Zmodp.zero) = x1 by ring.
have ->: Zmodp.add x2 Zmodp.zero = x2 by ring.
reflexivity.
Qed.

Lemma mul_left_distr : left_distributive mul add.
Proof.
move=> [x1 x2] [y1 y2] [z1 z2]. rewrite /mul /add /=. f_equal.
f_equal.
ring.
ring.
(* + apply val_inj => /=.
  rewrite Zmult_mod_idemp_l.
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
+ apply val_inj => /=.
  rewrite Zmult_mod_idemp_l.
  rewrite Zmult_mod_idemp_l.
  rewrite -Zplus_mod.
  rewrite -(Zplus_mod (x1 * z2)).
  rewrite -(Zplus_mod (y1 * z2)).
  rewrite -Zplus_mod.
  f_equal.
  ring. *)
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
apply/eqP; rewrite eqE; apply/eqP=> /=.
apply: esym. f_equal; apply val_inj => /=.
Qed.

Fact Hp_prime : prime p.
Proof. by unlock p; apply: primo. Qed.

Inductive Zinv_spec (x : type) : Type :=
| Zinv_spec_zero : x = zero -> Zinv_spec x
| Zinv_spec_unit : x <> zero -> forall y, (y * x)%R = one -> Zinv_spec x.

Fixpoint pow (n:nat) (x:type) := match n with
  | 0%nat => one
  | S n => (x * pow n x)%R
end.

Axiom Zinv_pow : forall (x :type), x <> zero -> pow (Z.to_nat (Z.pow p 2 - 1)%Z) x = one.

Lemma Zinv x : Zinv_spec x.
Proof.
case_eq (eqb x zero) ; move/eqb_spec.
+ move => -> ; exact: Zinv_spec_zero.
+ move=> Hx.
apply (@Zinv_spec_unit x Hx (pow (Z.to_nat (Z.pow p 2 - 2)) x)).
have := Zinv_pow Hx.
have ->: Z.to_nat (p ^ 2 - 1)%Z = (Z.to_nat (p ^ 2 - 2 + 1)%Z) by f_equal ; omega.
change (p ^2 - 2 + 1)%Z with (Z.succ (p^2 -2))%Z.
rewrite Z2Nat.inj_succ /=.
2: by rewrite /p -lock ; compute.
move => <-.
apply Zmodp2_ring.mul_comm.
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