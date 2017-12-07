From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice generic_quotient ssralg.
Require Import ZArith ZArith.Znumtheory.

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

Module Zmodp.
Section Zmodp.

Variable p : Z.
Hypothesis Hp : p > 0.

Definition betweenb x y z := (x <=? z) && (z <? y).

Inductive type := Zmodp x of betweenb 0 p x.

Lemma betweenbP x y z : reflect (x <= y < z) (betweenb x z y).
Proof. by apply/(iffP andP); case=> /Z.leb_spec0 H1 /Z.ltb_spec0 H2. Qed.

Lemma Z_mod_betweenb x y : y > 0 -> betweenb 0 y (x mod y).
Proof. by move=> H; apply/betweenbP; apply: Z_mod_lt. Qed.

Definition pi (x : Z) : type := Zmodp (Z_mod_betweenb x Hp).
Coercion repr (x : type) : Z := let: @Zmodp x _ := x in x.

Canonical Structure subType := [subType for repr].
Definition eqMixin := Eval hnf in [eqMixin of type by <:].
Canonical Structure eqType := Eval hnf in EqType type eqMixin.
Definition choiceMixin := Eval hnf in [choiceMixin of type by <:].
Canonical Structure choiceType := Eval hnf in ChoiceType type choiceMixin.
Definition countMixin := Eval hnf in [countMixin of type by <:].
Canonical Structure countType := Eval hnf in CountType type countMixin.

Lemma modZp (x : type) : x mod p = x.
Proof. by apply: Zmod_small; apply/betweenbP; case: x. Qed.

Lemma reprK (x : type) : pi x = x.
Proof. by apply: val_inj; apply: modZp. Qed.

Lemma piK (x : Z) : betweenb 0 p x -> repr (pi x) = x.
Proof. by move/betweenbP=> Hx /=; apply: Zmod_small. Qed.

Definition zero : type := pi 0.
Definition opp (x : type) : type := pi (p - x).
Definition add (x y : type) : type := pi (x + y).

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
by rewrite /= Zplus_mod_idemp_l Z.sub_add Z_mod_same.
Qed.

Definition zmodMixin := ZmodMixin add_assoc add_comm add_left_id add_left_inv.
Canonical Structure zmodType := Eval hnf in ZmodType type zmodMixin.

End Zmodp.

Section ZmodpRing.

Variable p : Z.
Hypothesis Hp : p > 1.

Lemma pgt_0 : p > 0.
Proof. by apply: (Zgt_trans _ 1). Qed.

(* TODO: Local Notations? *)
Notation type := (type p).
Notation pi := (pi pgt_0).
Notation zero := (zero pgt_0).
Notation add := (add pgt_0).

Definition one : type := pi 1.
Definition mul (x y : type) : type := pi (x * y).

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
rewrite Z.mod_1_l; last exact: Z.gt_lt.
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
by rewrite Zmod_0_l Zmod_1_l; last exact: Z.gt_lt.
Qed.

Definition ringMixin := Eval hnf in
  ComRingMixin mul_assoc mul_comm mul_left_id mul_left_distr one_neq_zero.
Canonical Structure ringType := Eval hnf in RingType type ringMixin.
Canonical Structure comRingType := Eval hnf in ComRingType type mul_comm.

End ZmodpRing.

Section ZmodpField.

Variable p : Z.
Hypothesis Hp : prime p.

Check FieldUnitMixin.

End ZmodpField.
End Zmodp.
