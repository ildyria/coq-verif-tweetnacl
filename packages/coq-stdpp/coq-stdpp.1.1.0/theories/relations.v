(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects definitions and theorems on abstract rewriting systems.
These are particularly useful as we define the operational semantics as a
small step semantics. This file defines a hint database [ars] containing
some theorems on abstract rewriting systems. *)
From Coq Require Import Wf_nat.
From stdpp Require Export tactics base.
Set Default Proof Using "Type".

(** * Definitions *)
Section definitions.
  Context `(R : relation A).

  (** An element is reducible if a step is possible. *)
  Definition red (x : A) := ∃ y, R x y.

  (** An element is in normal form if no further steps are possible. *)
  Definition nf (x : A) := ¬red x.

  (** The reflexive transitive closure. *)
  Inductive rtc : relation A :=
    | rtc_refl x : rtc x x
    | rtc_l x y z : R x y → rtc y z → rtc x z.

  (** The reflexive transitive closure for setoids. *)
  Inductive rtcS `{Equiv A} : relation A :=
    | rtcS_refl x y : x ≡ y → rtcS x y
    | rtcS_l x y z : R x y → rtcS y z → rtcS x z.

  (** Reductions of exactly [n] steps. *)
  Inductive nsteps : nat → relation A :=
    | nsteps_O x : nsteps 0 x x
    | nsteps_l n x y z : R x y → nsteps n y z → nsteps (S n) x z.

  (** Reduction of at most [n] steps. *)
  Inductive bsteps : nat → relation A :=
    | bsteps_refl n x : bsteps n x x
    | bsteps_l n x y z : R x y → bsteps n y z → bsteps (S n) x z.

  (** The transitive closure. *)
  Inductive tc : relation A :=
    | tc_once x y : R x y → tc x y
    | tc_l x y z : R x y → tc y z → tc x z.

  (** An element [x] is universally looping if all paths starting at [x]
  are infinite. *)
  CoInductive all_loop : A → Prop :=
    | all_loop_do_step x : red x → (∀ y, R x y → all_loop y) → all_loop x.

  (** An element [x] is existentally looping if some path starting at [x]
  is infinite. *)
  CoInductive ex_loop : A → Prop :=
    | ex_loop_do_step x y : R x y → ex_loop y → ex_loop x.
End definitions.

Hint Unfold nf red.

(** * General theorems *)
Section rtc.
  Context `{R : relation A}.

  Hint Constructors rtc nsteps bsteps tc.

  Global Instance rtc_reflexive: Reflexive (rtc R).
  Proof. exact (@rtc_refl A R). Qed.
  Lemma rtc_transitive x y z : rtc R x y → rtc R y z → rtc R x z.
  Proof. induction 1; eauto. Qed.
  Global Instance: Transitive (rtc R).
  Proof. exact rtc_transitive. Qed.
  Lemma rtc_once x y : R x y → rtc R x y.
  Proof. eauto. Qed.
  Lemma rtc_r x y z : rtc R x y → R y z → rtc R x z.
  Proof. intros. etrans; eauto. Qed.
  Lemma rtc_inv x z : rtc R x z → x = z ∨ ∃ y, R x y ∧ rtc R y z.
  Proof. inversion_clear 1; eauto. Qed.
  Lemma rtc_ind_l (P : A → Prop) (z : A)
    (Prefl : P z) (Pstep : ∀ x y, R x y → rtc R y z → P y → P x) :
    ∀ x, rtc R x z → P x.
  Proof. induction 1; eauto. Qed.
  Lemma rtc_ind_r_weak (P : A → A → Prop)
    (Prefl : ∀ x, P x x) (Pstep : ∀ x y z, rtc R x y → R y z → P x y → P x z) :
    ∀ x z, rtc R x z → P x z.
  Proof.
    cut (∀ y z, rtc R y z → ∀ x, rtc R x y → P x y → P x z).
    { eauto using rtc_refl. }
    induction 1; eauto using rtc_r.
  Qed.
  Lemma rtc_ind_r (P : A → Prop) (x : A)
    (Prefl : P x) (Pstep : ∀ y z, rtc R x y → R y z → P y → P z) :
    ∀ z, rtc R x z → P z.
  Proof.
    intros z p. revert x z p Prefl Pstep. refine (rtc_ind_r_weak _ _ _); eauto.
  Qed.
  Lemma rtc_inv_r x z : rtc R x z → x = z ∨ ∃ y, rtc R x y ∧ R y z.
  Proof. revert z. apply rtc_ind_r; eauto. Qed.

  Lemma nsteps_once x y : R x y → nsteps R 1 x y.
  Proof. eauto. Qed.
  Lemma nsteps_trans n m x y z :
    nsteps R n x y → nsteps R m y z → nsteps R (n + m) x z.
  Proof. induction 1; simpl; eauto. Qed.
  Lemma nsteps_r n x y z : nsteps R n x y → R y z → nsteps R (S n) x z.
  Proof. induction 1; eauto. Qed.
  Lemma nsteps_rtc n x y : nsteps R n x y → rtc R x y.
  Proof. induction 1; eauto. Qed.
  Lemma rtc_nsteps x y : rtc R x y → ∃ n, nsteps R n x y.
  Proof. induction 1; firstorder eauto. Qed.

  Lemma bsteps_once n x y : R x y → bsteps R (S n) x y.
  Proof. eauto. Qed.
  Lemma bsteps_plus_r n m x y :
    bsteps R n x y → bsteps R (n + m) x y.
  Proof. induction 1; simpl; eauto. Qed.
  Lemma bsteps_weaken n m x y :
    n ≤ m → bsteps R n x y → bsteps R m x y.
  Proof.
    intros. rewrite (Minus.le_plus_minus n m); auto using bsteps_plus_r.
  Qed.
  Lemma bsteps_plus_l n m x y :
    bsteps R n x y → bsteps R (m + n) x y.
  Proof. apply bsteps_weaken. auto with arith. Qed.
  Lemma bsteps_S n x y :  bsteps R n x y → bsteps R (S n) x y.
  Proof. apply bsteps_weaken. lia. Qed.
  Lemma bsteps_trans n m x y z :
    bsteps R n x y → bsteps R m y z → bsteps R (n + m) x z.
  Proof. induction 1; simpl; eauto using bsteps_plus_l. Qed.
  Lemma bsteps_r n x y z : bsteps R n x y → R y z → bsteps R (S n) x z.
  Proof. induction 1; eauto. Qed.
  Lemma bsteps_rtc n x y : bsteps R n x y → rtc R x y.
  Proof. induction 1; eauto. Qed.
  Lemma rtc_bsteps x y : rtc R x y → ∃ n, bsteps R n x y.
  Proof. induction 1; [exists 0; constructor|]. naive_solver eauto. Qed.
  Lemma bsteps_ind_r (P : nat → A → Prop) (x : A)
    (Prefl : ∀ n, P n x)
    (Pstep : ∀ n y z, bsteps R n x y → R y z → P n y → P (S n) z) :
    ∀ n z, bsteps R n x z → P n z.
  Proof.
    cut (∀ m y z, bsteps R m y z → ∀ n,
      bsteps R n x y → (∀ m', n ≤ m' ∧ m' ≤ n + m → P m' y) → P (n + m) z).
    { intros help ?. change n with (0 + n). eauto. }
    induction 1 as [|m x' y z p2 p3 IH]; [by eauto with arith|].
    intros n p1 H. rewrite <-plus_n_Sm.
    apply (IH (S n)); [by eauto using bsteps_r |].
    intros [|m'] [??]; [lia |]. apply Pstep with x'.
    - apply bsteps_weaken with n; intuition lia.
    - done.
    - apply H; intuition lia.
  Qed.

  Lemma tc_transitive x y z : tc R x y → tc R y z → tc R x z.
  Proof. induction 1; eauto. Qed.
  Global Instance: Transitive (tc R).
  Proof. exact tc_transitive. Qed.
  Lemma tc_r x y z : tc R x y → R y z → tc R x z.
  Proof. intros. etrans; eauto. Qed.
  Lemma tc_rtc_l x y z : rtc R x y → tc R y z → tc R x z.
  Proof. induction 1; eauto. Qed.
  Lemma tc_rtc_r x y z : tc R x y → rtc R y z → tc R x z.
  Proof. intros Hxy Hyz. revert x Hxy. induction Hyz; eauto using tc_r. Qed.
  Lemma tc_rtc x y : tc R x y → rtc R x y.
  Proof. induction 1; eauto. Qed.

  Lemma all_loop_red x : all_loop R x → red R x.
  Proof. destruct 1; auto. Qed.
  Lemma all_loop_step x y : all_loop R x → R x y → all_loop R y.
  Proof. destruct 1; auto. Qed.
  Lemma all_loop_rtc x y : all_loop R x → rtc R x y → all_loop R y.
  Proof. induction 2; eauto using all_loop_step. Qed.
  Lemma all_loop_alt x :
    all_loop R x ↔ ∀ y, rtc R x y → red R y.
  Proof.
    split; [eauto using all_loop_red, all_loop_rtc|].
    intros H. cut (∀ z, rtc R x z → all_loop R z); [eauto|].
    cofix FIX. constructor; eauto using rtc_r.
  Qed.
End rtc.

Hint Constructors rtc nsteps bsteps tc : ars.
Hint Resolve rtc_once rtc_r tc_r rtc_transitive tc_rtc_l tc_rtc_r
  tc_rtc bsteps_once bsteps_r bsteps_refl bsteps_trans : ars.

(** * Theorems on sub relations *)
Section subrel.
  Context {A} (R1 R2 : relation A).
  Notation subrel := (∀ x y, R1 x y → R2 x y).
  Lemma red_subrel x : subrel → red R1 x → red R2 x.
  Proof. intros ? [y ?]; eauto. Qed.
  Lemma nf_subrel x : subrel → nf R2 x → nf R1 x.
  Proof. intros ? H1 H2; destruct H1; by apply red_subrel. Qed.
  Lemma rtc_subrel x y : subrel → rtc R1 x y → rtc R2 x y.
  Proof. induction 2; [by apply rtc_refl|]. eapply rtc_l; eauto. Qed.
End subrel.

(** * Theorems on well founded relations *)
Notation wf := well_founded.
Definition wf_guard `{R : relation A} (n : nat) (wfR : wf R) : wf R :=
  Acc_intro_generator n wfR.

(* Generally we do not want [wf_guard] to be expanded (neither by tactics,
nor by conversion tests in the kernel), but in some cases we do need it for
computation (that is, we cannot make it opaque). We use the [Strategy]
command to make its expanding behavior less eager. *)
Strategy 100 [wf_guard].

Lemma wf_projected `{R1 : relation A} `(R2 : relation B) (f : A → B) :
  (∀ x y, R1 x y → R2 (f x) (f y)) →
  wf R2 → wf R1.
Proof.
  intros Hf Hwf.
  cut (∀ y, Acc R2 y → ∀ x, y = f x → Acc R1 x).
  { intros aux x. apply (aux (f x)); auto. }
  induction 1 as [y _ IH]. intros x ?. subst.
  constructor. intros. apply (IH (f y)); auto.
Qed.

Lemma Fix_F_proper `{R : relation A} (B : A → Type) (E : ∀ x, relation (B x))
    (F : ∀ x, (∀ y, R y x → B y) → B x)
    (HF : ∀ (x : A) (f g : ∀ y, R y x → B y),
      (∀ y Hy Hy', E _ (f y Hy) (g y Hy')) → E _ (F x f) (F x g))
    (x : A) (acc1 acc2 : Acc R x) :
  E _ (Fix_F B F acc1) (Fix_F B F acc2).
Proof. revert x acc1 acc2. fix 2. intros x [acc1] [acc2]; simpl; auto. Qed.

Lemma Fix_unfold_rel `{R: relation A} (wfR: wf R) (B: A → Type) (E: ∀ x, relation (B x))
      (F: ∀ x, (∀ y, R y x → B y) → B x)
      (HF: ∀ (x: A) (f g: ∀ y, R y x → B y),
             (∀ y Hy Hy', E _ (f y Hy) (g y Hy')) → E _ (F x f) (F x g))
      (x: A):
  E _ (Fix wfR B F x) (F x (λ y _, Fix wfR B F y)).
Proof.
  unfold Fix.
  destruct (wfR x); cbn.
  apply HF; intros.
  apply Fix_F_proper; auto.
Qed.
