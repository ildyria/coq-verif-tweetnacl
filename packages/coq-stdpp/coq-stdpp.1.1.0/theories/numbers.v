(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects some trivial facts on the Coq types [nat] and [N] for
natural numbers, and the type [Z] for integers. It also declares some useful
notations. *)
From Coq Require Export EqdepFacts PArith NArith ZArith NPeano.
From Coq Require Import QArith Qcanon.
From stdpp Require Export base decidable option.
Set Default Proof Using "Type".
Open Scope nat_scope.

Coercion Z.of_nat : nat >-> Z.
Instance comparison_eq_dec : EqDecision comparison.
Proof. solve_decision. Defined.

(** * Notations and properties of [nat] *)
Arguments minus !_ !_ / : assert.
Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y ≤ z ≤ z'"
  (at level 70, y at next level, z at next level).

Infix "≤" := le : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%nat : nat_scope.
Notation "(≤)" := le (only parsing) : nat_scope.
Notation "(<)" := lt (only parsing) : nat_scope.

Infix "`div`" := Nat.div (at level 35) : nat_scope.
Infix "`mod`" := Nat.modulo (at level 35) : nat_scope.
Infix "`max`" := Nat.max (at level 35) : nat_scope.
Infix "`min`" := Nat.min (at level 35) : nat_scope.

Instance nat_eq_dec: EqDecision nat := eq_nat_dec.
Instance nat_le_dec: RelDecision le := le_dec.
Instance nat_lt_dec: RelDecision lt := lt_dec.
Instance nat_inhabited: Inhabited nat := populate 0%nat.
Instance S_inj: Inj (=) (=) S.
Proof. by injection 1. Qed.
Instance nat_le_po: PartialOrder (≤).
Proof. repeat split; repeat intro; auto with lia. Qed.

Instance nat_le_pi: ∀ x y : nat, ProofIrrel (x ≤ y).
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
    y = y' → eq_dep nat (le x) y p y' q) as aux.
  { fix 3. intros x ? [|y p] ? [|y' q].
    - done.
    - clear nat_le_pi. intros; exfalso; auto with lia.
    - clear nat_le_pi. intros; exfalso; auto with lia.
    - injection 1. intros Hy. by case (nat_le_pi x y p y' q Hy). }
  intros x y p q.
  by apply (Eqdep_dec.eq_dep_eq_dec (λ x y, decide (x = y))), aux.
Qed.
Instance nat_lt_pi: ∀ x y : nat, ProofIrrel (x < y).
Proof. apply _. Qed.

Lemma nat_le_sum (x y : nat) : x ≤ y ↔ ∃ z, y = x + z.
Proof. split. exists (y - x); lia. intros [z ->]; lia. Qed.

Lemma Nat_lt_succ_succ n : n < S (S n).
Proof. auto with arith. Qed.
Lemma Nat_mul_split_l n x1 x2 y1 y2 :
  x2 < n → y2 < n → x1 * n + x2 = y1 * n + y2 → x1 = y1 ∧ x2 = y2.
Proof.
  intros Hx2 Hy2 E. cut (x1 = y1); [intros; subst;lia |].
  revert y1 E. induction x1; simpl; intros [|?]; simpl; auto with lia.
Qed.
Lemma Nat_mul_split_r n x1 x2 y1 y2 :
  x1 < n → y1 < n → x1 + x2 * n = y1 + y2 * n → x1 = y1 ∧ x2 = y2.
Proof. intros. destruct (Nat_mul_split_l n x2 x1 y2 y1); auto with lia. Qed.

Notation lcm := Nat.lcm.
Notation divide := Nat.divide.
Notation "( x | y )" := (divide x y) : nat_scope.
Instance Nat_divide_dec : RelDecision Nat.divide.
Proof.
  refine (λ x y, cast_if (decide (lcm x y = y))); by rewrite Nat.divide_lcm_iff.
Defined.
Instance: PartialOrder divide.
Proof.
  repeat split; try apply _. intros ??. apply Nat.divide_antisym_nonneg; lia.
Qed.
Hint Extern 0 (_ | _) => reflexivity.
Lemma Nat_divide_ne_0 x y : (x | y) → y ≠ 0 → x ≠ 0.
Proof. intros Hxy Hy ->. by apply Hy, Nat.divide_0_l. Qed.

Lemma Nat_iter_S {A} n (f: A → A) x : Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. done. Qed.
Lemma Nat_iter_S_r {A} n (f: A → A) x : Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. induction n; f_equal/=; auto. Qed.
Lemma Nat_iter_ind {A} (P : A → Prop) f x k :
  P x → (∀ y, P y → P (f y)) → P (Nat.iter k f x).
Proof. induction k; simpl; auto. Qed.

Definition sum_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x + go l
  end.
Notation sum_list := (sum_list_with id).

Definition max_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x `max` go l
  end.
Notation max_list := (max_list_with id).

(** * Notations and properties of [positive] *)
Open Scope positive_scope.

Infix "≤" := Pos.le : positive_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : positive_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : positive_scope.
Notation "(≤)" := Pos.le (only parsing) : positive_scope.
Notation "(<)" := Pos.lt (only parsing) : positive_scope.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Arguments Pos.of_nat : simpl never.
Arguments Pmult : simpl never.

Instance positive_eq_dec: EqDecision positive := Pos.eq_dec.
Instance positive_le_dec: RelDecision Pos.le.
Proof. refine (λ x y, decide ((x ?= y) ≠ Gt)). Defined.
Instance positive_lt_dec: RelDecision Pos.lt.
Proof. refine (λ x y, decide ((x ?= y) = Lt)). Defined.
Instance positive_inhabited: Inhabited positive := populate 1.

Instance maybe_xO : Maybe xO := λ p, match p with p~0 => Some p | _ => None end.
Instance maybe_xI : Maybe xI := λ p, match p with p~1 => Some p | _ => None end.
Instance xO_inj : Inj (=) (=) (~0).
Proof. by injection 1. Qed.
Instance xI_inj : Inj (=) (=) (~1).
Proof. by injection 1. Qed.

(** Since [positive] represents lists of bits, we define list operations
on it. These operations are in reverse, as positives are treated as snoc
lists instead of cons lists. *)
Fixpoint Papp (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => (Papp p1 p2)~0
  | p2~1 => (Papp p1 p2)~1
  end.
Infix "++" := Papp : positive_scope.
Notation "(++)" := Papp (only parsing) : positive_scope.
Notation "( p ++)" := (Papp p) (only parsing) : positive_scope.
Notation "(++ q )" := (λ p, Papp p q) (only parsing) : positive_scope.

Fixpoint Preverse_go (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => Preverse_go (p1~0) p2
  | p2~1 => Preverse_go (p1~1) p2
  end.
Definition Preverse : positive → positive := Preverse_go 1.

Global Instance Papp_1_l : LeftId (=) 1 (++).
Proof. intros p. by induction p; intros; f_equal/=. Qed.
Global Instance Papp_1_r : RightId (=) 1 (++).
Proof. done. Qed.
Global Instance Papp_assoc : Assoc (=) (++).
Proof. intros ?? p. by induction p; intros; f_equal/=. Qed.
Global Instance Papp_inj p : Inj (=) (=) (++ p).
Proof. intros ???. induction p; simplify_eq; auto. Qed.

Lemma Preverse_go_app p1 p2 p3 :
  Preverse_go p1 (p2 ++ p3) = Preverse_go p1 p3 ++ Preverse_go 1 p2.
Proof.
  revert p3 p1 p2.
  cut (∀ p1 p2 p3, Preverse_go (p2 ++ p3) p1 = p2 ++ Preverse_go p3 p1).
  { by intros go p3; induction p3; intros p1 p2; simpl; auto; rewrite <-?go. }
  intros p1; induction p1 as [p1 IH|p1 IH|]; intros p2 p3; simpl; auto.
  - apply (IH _ (_~1)).
  - apply (IH _ (_~0)).
Qed.
Lemma Preverse_app p1 p2 : Preverse (p1 ++ p2) = Preverse p2 ++ Preverse p1.
Proof. unfold Preverse. by rewrite Preverse_go_app. Qed.
Lemma Preverse_xO p : Preverse (p~0) = (1~0) ++ Preverse p.
Proof Preverse_app p (1~0).
Lemma Preverse_xI p : Preverse (p~1) = (1~1) ++ Preverse p.
Proof Preverse_app p (1~1).

Fixpoint Plength (p : positive) : nat :=
  match p with 1 => 0%nat | p~0 | p~1 => S (Plength p) end.
Lemma Papp_length p1 p2 : Plength (p1 ++ p2) = (Plength p2 + Plength p1)%nat.
Proof. by induction p2; f_equal/=. Qed.

Lemma Plt_sum (x y : positive) : x < y ↔ ∃ z, y = x + z.
Proof.
  split.
  - exists (y - x)%positive. symmetry. apply Pplus_minus. lia.
  - intros [z ->]. lia.
Qed.

Close Scope positive_scope.

(** * Notations and properties of [N] *)
Infix "≤" := N.le : N_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%N : N_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%N : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.
Notation "(<)" := N.lt (only parsing) : N_scope.
Infix "`div`" := N.div (at level 35) : N_scope.
Infix "`mod`" := N.modulo (at level 35) : N_scope.

Arguments N.add : simpl never.

Instance Npos_inj : Inj (=) (=) Npos.
Proof. by injection 1. Qed.

Instance N_eq_dec: EqDecision N := N.eq_dec.
Program Instance N_le_dec : RelDecision N.le := λ x y,
  match Ncompare x y with Gt => right _ | _ => left _ end.
Solve Obligations with naive_solver.
Program Instance N_lt_dec : RelDecision N.lt := λ x y,
  match Ncompare x y with Lt => left _ | _ => right _ end.
Solve Obligations with naive_solver.
Instance N_inhabited: Inhabited N := populate 1%N.
Instance N_le_po: PartialOrder (≤)%N.
Proof.
  repeat split; red. apply N.le_refl. apply N.le_trans. apply N.le_antisymm.
Qed.
Hint Extern 0 (_ ≤ _)%N => reflexivity.

(** * Notations and properties of [Z] *)
Open Scope Z_scope.

Infix "≤" := Z.le : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Notation "(<)" := Z.lt (only parsing) : Z_scope.

Infix "`div`" := Z.div (at level 35) : Z_scope.
Infix "`mod`" := Z.modulo (at level 35) : Z_scope.
Infix "`quot`" := Z.quot (at level 35) : Z_scope.
Infix "`rem`" := Z.rem (at level 35) : Z_scope.
Infix "≪" := Z.shiftl (at level 35) : Z_scope.
Infix "≫" := Z.shiftr (at level 35) : Z_scope.

Instance Zpos_inj : Inj (=) (=) Zpos.
Proof. by injection 1. Qed.
Instance Zneg_inj : Inj (=) (=) Zneg.
Proof. by injection 1. Qed.

Instance Z_of_nat_inj : Inj (=) (=) Z.of_nat.
Proof. intros n1 n2. apply Nat2Z.inj. Qed.

Instance Z_eq_dec: EqDecision Z := Z.eq_dec.
Instance Z_le_dec: RelDecision Z.le := Z_le_dec.
Instance Z_lt_dec: RelDecision Z.lt := Z_lt_dec.
Instance Z_inhabited: Inhabited Z := populate 1.
Instance Z_le_po : PartialOrder (≤).
Proof.
  repeat split; red. apply Z.le_refl. apply Z.le_trans. apply Z.le_antisymm.
Qed.

Lemma Z_pow_pred_r n m : 0 < m → n * n ^ (Z.pred m) = n ^ m.
Proof.
  intros. rewrite <-Z.pow_succ_r, Z.succ_pred. done. by apply Z.lt_le_pred.
Qed.
Lemma Z_quot_range_nonneg k x y : 0 ≤ x < k → 0 < y → 0 ≤ x `quot` y < k.
Proof.
  intros [??] ?.
  destruct (decide (y = 1)); subst; [rewrite Z.quot_1_r; auto |].
  destruct (decide (x = 0)); subst; [rewrite Z.quot_0_l; auto with lia |].
  split. apply Z.quot_pos; lia. trans x; auto. apply Z.quot_lt; lia.
Qed.

(* Note that we cannot disable simpl for [Z.of_nat] as that would break
tactics as [lia]. *)
Arguments Z.to_nat : simpl never.
Arguments Z.mul : simpl never.
Arguments Z.add : simpl never.
Arguments Z.opp : simpl never.
Arguments Z.pow : simpl never.
Arguments Z.div : simpl never.
Arguments Z.modulo : simpl never.
Arguments Z.quot : simpl never.
Arguments Z.rem : simpl never.

Lemma Z_to_nat_neq_0_pos x : Z.to_nat x ≠ 0%nat → 0 < x.
Proof. by destruct x. Qed.
Lemma Z_to_nat_neq_0_nonneg x : Z.to_nat x ≠ 0%nat → 0 ≤ x.
Proof. by destruct x. Qed.
Lemma Z_mod_pos x y : 0 < y → 0 ≤ x `mod` y.
Proof. apply Z.mod_pos_bound. Qed.

Hint Resolve Z.lt_le_incl : zpos.
Hint Resolve Z.add_nonneg_pos Z.add_pos_nonneg Z.add_nonneg_nonneg : zpos.
Hint Resolve Z.mul_nonneg_nonneg Z.mul_pos_pos : zpos.
Hint Resolve Z.pow_pos_nonneg Z.pow_nonneg: zpos.
Hint Resolve Z_mod_pos Z.div_pos : zpos.
Hint Extern 1000 => lia : zpos.

Lemma Z_to_nat_nonpos x : x ≤ 0 → Z.to_nat x = 0%nat.
Proof. destruct x; simpl; auto using Z2Nat.inj_neg. by intros []. Qed.
Lemma Z2Nat_inj_pow (x y : nat) : Z.of_nat (x ^ y) = x ^ y.
Proof.
  induction y as [|y IH]; [by rewrite Z.pow_0_r, Nat.pow_0_r|].
  by rewrite Nat.pow_succ_r, Nat2Z.inj_succ, Z.pow_succ_r,
    Nat2Z.inj_mul, IH by auto with zpos.
Qed.
Lemma Nat2Z_divide n m : (Z.of_nat n | Z.of_nat m) ↔ (n | m)%nat.
Proof.
  split.
  - rewrite <-(Nat2Z.id m) at 2; intros [i ->]; exists (Z.to_nat i).
    destruct (decide (0 ≤ i)%Z).
    { by rewrite Z2Nat.inj_mul, Nat2Z.id by lia. }
    by rewrite !Z_to_nat_nonpos by auto using Z.mul_nonpos_nonneg with lia.
  - intros [i ->]. exists (Z.of_nat i). by rewrite Nat2Z.inj_mul.
Qed.
Lemma Z2Nat_divide n m :
  0 ≤ n → 0 ≤ m → (Z.to_nat n | Z.to_nat m)%nat ↔ (n | m).
Proof. intros. by rewrite <-Nat2Z_divide, !Z2Nat.id by done. Qed.
Lemma Z2Nat_inj_div x y : Z.of_nat (x `div` y) = x `div` y.
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.div_unique with (x `mod` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Lemma Z2Nat_inj_mod x y : Z.of_nat (x `mod` y) = x `mod` y.
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.mod_unique with (x `div` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Close Scope Z_scope.

(** * Injectivity of casts *)
Instance N_of_nat_inj: Inj (=) (=) N.of_nat := Nat2N.inj.
Instance nat_of_N_inj: Inj (=) (=) N.to_nat := N2Nat.inj.
Instance nat_of_pos_inj: Inj (=) (=) Pos.to_nat := Pos2Nat.inj.
Instance pos_of_Snat_inj: Inj (=) (=) Pos.of_succ_nat := SuccNat2Pos.inj.
Instance Z_of_N_inj: Inj (=) (=) Z.of_N := N2Z.inj.
(* Add others here. *)

(** * Notations and properties of [Qc] *)
Open Scope Qc_scope.
Delimit Scope Qc_scope with Qc.
Notation "1" := (Q2Qc 1) : Qc_scope.
Notation "2" := (1+1) : Qc_scope.
Notation "- 1" := (Qcopp 1) : Qc_scope.
Notation "- 2" := (Qcopp 2) : Qc_scope.
Notation "x - y" := (x + -y) : Qc_scope.
Notation "x / y" := (x * /y) : Qc_scope.
Infix "≤" := Qcle : Qc_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Qc_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Qc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Qc_scope.
Notation "(≤)" := Qcle (only parsing) : Qc_scope.
Notation "(<)" := Qclt (only parsing) : Qc_scope.

Hint Extern 1 (_ ≤ _) => reflexivity || discriminate.
Arguments Qred : simpl never.

Instance Qc_eq_dec: EqDecision Qc := Qc_eq_dec.
Program Instance Qc_le_dec: RelDecision Qcle := λ x y,
  if Qclt_le_dec y x then right _ else left _.
Next Obligation. intros x y; apply Qclt_not_le. Qed.
Next Obligation. done. Qed.
Program Instance Qc_lt_dec: RelDecision Qclt := λ x y,
  if Qclt_le_dec x y then left _ else right _.
Solve Obligations with done.
Next Obligation. intros x y; apply Qcle_not_lt. Qed.

Instance: PartialOrder (≤).
Proof.
  repeat split; red. apply Qcle_refl. apply Qcle_trans. apply Qcle_antisym.
Qed.
Instance: StrictOrder (<).
Proof.
  split; red. intros x Hx. by destruct (Qclt_not_eq x x). apply Qclt_trans.
Qed.
Lemma Qcmult_0_l x : 0 * x = 0.
Proof. ring. Qed.
Lemma Qcmult_0_r x : x * 0 = 0.
Proof. ring. Qed.
Lemma Qcplus_diag x : (x + x)%Qc = (2 * x)%Qc.
Proof. ring. Qed.
Lemma Qcle_ngt (x y : Qc) : x ≤ y ↔ ¬y < x.
Proof. split; auto using Qcle_not_lt, Qcnot_lt_le. Qed.
Lemma Qclt_nge (x y : Qc) : x < y ↔ ¬y ≤ x.
Proof. split; auto using Qclt_not_le, Qcnot_le_lt. Qed.
Lemma Qcplus_le_mono_l (x y z : Qc) : x ≤ y ↔ z + x ≤ z + y.
Proof.
  split; intros.
  - by apply Qcplus_le_compat.
  - replace x with ((0 - z) + (z + x)) by ring.
    replace y with ((0 - z) + (z + y)) by ring.
    by apply Qcplus_le_compat.
Qed.
Lemma Qcplus_le_mono_r (x y z : Qc) : x ≤ y ↔ x + z ≤ y + z.
Proof. rewrite !(Qcplus_comm _ z). apply Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_l (x y z : Qc) : x < y ↔ z + x < z + y.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_r (x y z : Qc) : x < y ↔ x + z < y + z.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_r. Qed.
Instance: Inj (=) (=) Qcopp.
Proof.
  intros x y H. by rewrite <-(Qcopp_involutive x), H, Qcopp_involutive.
Qed.
Instance: ∀ z, Inj (=) (=) (Qcplus z).
Proof.
  intros z x y H. by apply (anti_symm (≤));
    rewrite (Qcplus_le_mono_l _ _ z), H.
Qed.
Instance: ∀ z, Inj (=) (=) (λ x, x + z).
Proof.
  intros z x y H. by apply (anti_symm (≤));
    rewrite (Qcplus_le_mono_r _ _ z), H.
Qed.
Lemma Qcplus_pos_nonneg (x y : Qc) : 0 < x → 0 ≤ y → 0 < x + y.
Proof.
  intros. apply Qclt_le_trans with (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonneg_pos (x y : Qc) : 0 ≤ x → 0 < y → 0 < x + y.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_pos_nonneg. Qed. 
Lemma Qcplus_pos_pos (x y : Qc) : 0 < x → 0 < y → 0 < x + y.
Proof. auto using Qcplus_pos_nonneg, Qclt_le_weak. Qed.
Lemma Qcplus_nonneg_nonneg (x y : Qc) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
Proof.
  intros. trans (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_neg_nonpos (x y : Qc) : x < 0 → y ≤ 0 → x + y < 0.
Proof.
  intros. apply Qcle_lt_trans with (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonpos_neg (x y : Qc) : x ≤ 0 → y < 0 → x + y < 0.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_neg_nonpos. Qed.
Lemma Qcplus_neg_neg (x y : Qc) : x < 0 → y < 0 → x + y < 0.
Proof. auto using Qcplus_nonpos_neg, Qclt_le_weak. Qed.
Lemma Qcplus_nonpos_nonpos (x y : Qc) : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof.
  intros. trans (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcmult_le_mono_nonneg_l x y z : 0 ≤ z → x ≤ y → z * x ≤ z * y.
Proof. intros. rewrite !(Qcmult_comm z). by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_nonneg_r x y z : 0 ≤ z → x ≤ y → x * z ≤ y * z.
Proof. intros. by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_pos_l x y z : 0 < z → x ≤ y ↔ z * x ≤ z * y.
Proof.
  split; auto using Qcmult_le_mono_nonneg_l, Qclt_le_weak.
  rewrite !Qcle_ngt, !(Qcmult_comm z).
  intuition auto using Qcmult_lt_compat_r.
Qed.
Lemma Qcmult_le_mono_pos_r x y z : 0 < z → x ≤ y ↔ x * z ≤ y * z.
Proof. rewrite !(Qcmult_comm _ z). by apply Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_l x y z : 0 < z → x < y ↔ z * x < z * y.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_r x y z : 0 < z → x < y ↔ x * z < y * z.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_r. Qed.
Lemma Qcmult_pos_pos x y : 0 < x → 0 < y → 0 < x * y.
Proof.
  intros. apply Qcle_lt_trans with (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_lt_mono_pos_r.
Qed.
Lemma Qcmult_nonneg_nonneg x y : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof.
  intros. trans (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_le_mono_nonneg_r.
Qed.

Lemma inject_Z_Qred n : Qred (inject_Z n) = inject_Z n.
Proof. apply Qred_identity; auto using Z.gcd_1_r. Qed.
Coercion Qc_of_Z (n : Z) : Qc := Qcmake _ (inject_Z_Qred n).
Lemma Z2Qc_inj_0 : Qc_of_Z 0 = 0.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj_1 : Qc_of_Z 1 = 1.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj_2 : Qc_of_Z 2 = 2.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj n m : Qc_of_Z n = Qc_of_Z m → n = m.
Proof. by injection 1. Qed.
Lemma Z2Qc_inj_iff n m : Qc_of_Z n = Qc_of_Z m ↔ n = m.
Proof. split. auto using Z2Qc_inj. by intros ->. Qed.
Lemma Z2Qc_inj_le n m : (n ≤ m)%Z ↔ Qc_of_Z n ≤ Qc_of_Z m.
Proof. by rewrite Zle_Qle. Qed.
Lemma Z2Qc_inj_lt n m : (n < m)%Z ↔ Qc_of_Z n < Qc_of_Z m.
Proof. by rewrite Zlt_Qlt. Qed.
Lemma Z2Qc_inj_add n m : Qc_of_Z (n + m) = Qc_of_Z n + Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_plus. Qed.
Lemma Z2Qc_inj_mul n m : Qc_of_Z (n * m) = Qc_of_Z n * Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_mult. Qed.
Lemma Z2Qc_inj_opp n : Qc_of_Z (-n) = -Qc_of_Z n.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_opp. Qed.
Lemma Z2Qc_inj_sub n m : Qc_of_Z (n - m) = Qc_of_Z n - Qc_of_Z m.
Proof.
  apply Qc_is_canon; simpl.
  by rewrite !Qred_correct, <-inject_Z_opp, <-inject_Z_plus.
Qed.
Close Scope Qc_scope.

(** * Positive rationals *)
(** The theory of positive rationals is very incomplete. We merely provide
some operations and theorems that are relevant for fractional permissions. *)
Record Qp := mk_Qp { Qp_car :> Qc ; Qp_prf : (0 < Qp_car)%Qc }.
Hint Resolve Qp_prf.
Delimit Scope Qp_scope with Qp.
Bind Scope Qp_scope with Qp.
Arguments Qp_car _%Qp : assert.

Definition Qp_one : Qp := mk_Qp 1 eq_refl.
Program Definition Qp_plus (x y : Qp) : Qp := mk_Qp (x + y) _.
Next Obligation. by intros x y; apply Qcplus_pos_pos. Qed.
Definition Qp_minus (x y : Qp) : option Qp :=
  let z := (x - y)%Qc in
  match decide (0 < z)%Qc with left Hz => Some (mk_Qp z Hz) | _ => None end.
Program Definition Qp_mult (x y : Qp) : Qp := mk_Qp (x * y) _.
Next Obligation. intros x y. apply Qcmult_pos_pos; apply Qp_prf. Qed.

Program Definition Qp_div (x : Qp) (y : positive) : Qp := mk_Qp (x / Zpos y) _.
Next Obligation.
  intros x y. assert (0 < Zpos y)%Qc.
  { apply (Z2Qc_inj_lt 0%Z (Zpos y)), Pos2Z.is_pos. }
  by rewrite (Qcmult_lt_mono_pos_r _ _ (Zpos y)%Z), Qcmult_0_l,
    <-Qcmult_assoc, Qcmult_inv_l, Qcmult_1_r.
Qed.

Notation "1" := Qp_one : Qp_scope.
Infix "+" := Qp_plus : Qp_scope.
Infix "-" := Qp_minus : Qp_scope.
Infix "*" := Qp_mult : Qp_scope.
Infix "/" := Qp_div : Qp_scope.

Lemma Qp_eq x y : x = y ↔ Qp_car x = Qp_car y.
Proof.
  split; [by intros ->|].
  destruct x, y; intros; simplify_eq/=; f_equal; apply (proof_irrel _).
Qed.

Instance Qp_inhabited : Inhabited Qp := populate 1%Qp.
Instance Qp_eq_dec : EqDecision Qp.
Proof.
 refine (λ x y, cast_if (decide (Qp_car x = Qp_car y))); by rewrite Qp_eq.
Defined.

Instance Qp_plus_assoc : Assoc (=) Qp_plus.
Proof. intros x y z; apply Qp_eq, Qcplus_assoc. Qed.
Instance Qp_plus_comm : Comm (=) Qp_plus.
Proof. intros x y; apply Qp_eq, Qcplus_comm. Qed.

Lemma Qp_minus_diag x : (x - x)%Qp = None.
Proof. unfold Qp_minus. by rewrite Qcplus_opp_r. Qed.
Lemma Qp_op_minus x y : ((x + y) - x)%Qp = Some y.
Proof.
  unfold Qp_minus; simpl.
  rewrite (Qcplus_comm x), <- Qcplus_assoc, Qcplus_opp_r, Qcplus_0_r.
  destruct (decide _) as [|[]]; auto. by f_equal; apply Qp_eq.
Qed.

Instance Qp_mult_assoc : Assoc (=) Qp_mult.
Proof. intros x y z; apply Qp_eq, Qcmult_assoc. Qed.
Instance Qp_mult_comm : Comm (=) Qp_mult.
Proof. intros x y; apply Qp_eq, Qcmult_comm. Qed.
Lemma Qp_mult_plus_distr_r x y z: (x * (y + z) = x * y + x * z)%Qp.
Proof. apply Qp_eq, Qcmult_plus_distr_r. Qed.
Lemma Qp_mult_plus_distr_l x y z: ((x + y) * z = x * z + y * z)%Qp.
Proof. apply Qp_eq, Qcmult_plus_distr_l. Qed.
Lemma Qp_mult_1_l x: (1 * x)%Qp = x.
Proof. apply Qp_eq, Qcmult_1_l. Qed.
Lemma Qp_mult_1_r x: (x * 1)%Qp = x.
Proof. apply Qp_eq, Qcmult_1_r. Qed.

Lemma Qp_div_1 x : (x / 1 = x)%Qp.
Proof.
  apply Qp_eq; simpl.
  rewrite <-(Qcmult_div_r x 1) at 2 by done. by rewrite Qcmult_1_l.
Qed.
Lemma Qp_div_S x y : (x / (2 * y) + x / (2 * y) = x / y)%Qp.
Proof.
  apply Qp_eq; simpl.
  rewrite <-Qcmult_plus_distr_l, Pos2Z.inj_mul, Z2Qc_inj_mul, Z2Qc_inj_2.
  rewrite Qcplus_diag. by field_simplify.
Qed.
Lemma Qp_div_2 x : (x / 2 + x / 2 = x)%Qp.
Proof.
  change 2%positive with (2 * 1)%positive. by rewrite Qp_div_S, Qp_div_1.
Qed.

Lemma Qp_lt_sum (x y : Qp) : (x < y)%Qc ↔ ∃ z, y = (x + z)%Qp.
Proof.
  split.
  - intros Hlt%Qclt_minus_iff. exists (mk_Qp (y - x) Hlt). apply Qp_eq; simpl.
    by rewrite (Qcplus_comm y), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
  - intros [z ->]; simpl.
    rewrite <-(Qcplus_0_r x) at 1. apply Qcplus_lt_mono_l, Qp_prf.
Qed.

Lemma Qp_lower_bound q1 q2 : ∃ q q1' q2', (q1 = q + q1' ∧ q2 = q + q2')%Qp.
Proof.
  revert q1 q2. cut (∀ q1 q2 : Qp, (q1 ≤ q2)%Qc →
    ∃ q q1' q2', (q1 = q + q1' ∧ q2 = q + q2')%Qp).
  { intros help q1 q2.
    destruct (Qc_le_dec q1 q2) as [LE|LE%Qclt_nge%Qclt_le_weak]; [by eauto|].
    destruct (help q2 q1) as (q&q1'&q2'&?&?); eauto. }
  intros q1 q2 Hq. exists (q1 / 2)%Qp, (q1 / 2)%Qp.
  assert (0 < q2 - q1 / 2)%Qc as Hq2'.
  { eapply Qclt_le_trans; [|by apply Qcplus_le_mono_r, Hq].
    replace (q1 - q1 / 2)%Qc with (q1 * (1 - 1/2))%Qc by ring.
    replace 0%Qc with (0 * (1-1/2))%Qc by ring. by apply Qcmult_lt_compat_r. }
  exists (mk_Qp (q2 - q1 / 2%Z) Hq2'). split; [by rewrite Qp_div_2|].
  apply Qp_eq; simpl. ring.
Qed.

Lemma Qp_not_plus_q_ge_1 (q: Qp): ¬ ((1 + q)%Qp ≤ 1%Qp)%Qc.
Proof.
  intros Hle.
  apply (Qcplus_le_mono_l q 0 1) in Hle.
  apply Qcle_ngt in Hle. apply Hle, Qp_prf.
Qed.

Lemma Qp_ge_0 (q: Qp): (0 ≤ q)%Qc.
Proof. apply Qclt_le_weak, Qp_prf. Qed.
