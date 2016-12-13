Require Export Tools.
Require Export ZofList.
Require Export Calc_lib.
Require Export notations.

Open Scope Z.

(*Notation "A :𝓖𝓕" := (A mod (2^255 - 19)) (at level 80, right associativity).*)

Lemma t2256is38 : (2^256 :𝓖𝓕 ) = (38 :𝓖𝓕).
Proof.
  compute.
  reflexivity.
(*
change 38 with (2 * 19).
change 256 with (Z.succ 255).
rewrite Z.pow_succ_r ; try omega.
rewrite <- Zmult_mod_idemp_r.
symmetry.
rewrite <- Zmult_mod_idemp_r.
f_equal.
*)
Qed.

Definition reduce n := 
  let c := n / 2^(256) in
  n + 38 * c - 2^(256) * c.

Lemma reduceGF : forall m, (reduce m :𝓖𝓕) = (m :𝓖𝓕).
Proof.
  intro m.
  unfold reduce.
  rewrite <- Zminus_mod_idemp_r.
  rewrite <- Zminus_mod_idemp_l.
  rewrite <- Zplus_mod_idemp_r.
  rewrite <- Zmult_mod_idemp_l.
  rewrite <- t2256is38.
  rewrite <- Zplus_mod_idemp_l.
  rewrite Zminus_mod_idemp_l.
  rewrite Zmult_mod_idemp_l.
  rewrite <- Z.add_sub_assoc.
  rewrite <- Zminus_diag_reverse.
  rewrite <- Zplus_0_r_reverse.
  rewrite Zmod_mod.
  reflexivity.
Qed.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma res_pos: forall (a:Z), 0 <= a - Z.shiftl (Z.shiftr a n) n.
Proof.
  intro a.
  rewrite Z.shiftr_div_pow2 by omega.
  rewrite Z.shiftl_mul_pow2 by omega.
  apply Zle_minus_le_0.
  rewrite Z.mul_comm.
  apply Z.mul_div_le.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
Qed.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Definition getCarry (m:Z) : Z :=  Z.shiftr m n.

(* Compute (getCarry (Z.pow 2 18)). *)

Definition getResidue (m:Z) : Z := m mod 2^n.

Lemma getResidue_mod: forall (m:Z), getResidue m = m - Z.shiftl (Z.shiftr m n) n.
Proof.
  intro a.
  unfold getResidue.
  rewrite Z.shiftr_div_pow2 by omega.
  rewrite Z.shiftl_mul_pow2 by omega.
  apply Zplus_minus_eq.
  rewrite Z.mul_comm.
  apply Z_div_mod_eq.
  apply pown0.
  assumption.
Qed.

Lemma getResidue_0 : getResidue 0 = 0.
Proof.
  go.
Qed.

Lemma getCarry_0 : getCarry 0 = 0.
Proof.
  apply Z.shiftr_0_l.
Qed.

Lemma getResidue_bounds : forall m:Z, 0 <= getResidue m < 2^n.
Proof.
  intro m.
  unfold getResidue.
  apply Z_mod_lt.
  apply pown0.
  assumption.
Qed.

Lemma mod_div: forall m:Z, m mod 2 ^ n + 2 ^ n * (m / 2 ^ n) = m.
Proof.
  intro.
  rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq.
  apply pown0.
  assumption.
Qed.

Lemma residuteCarry : forall m:Z, getResidue m + 2^n *getCarry m = m.
Proof.
  intro m.
  unfold getResidue.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 ; try omega.
  apply mod_div.
Qed.

Lemma getCarryMonotone_pos : forall m, m > 0 -> getCarry m < m.
Proof.
  intros m Hm.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 ; try omega.
  induction m ; go.
  - apply Z_div_lt ; go.
  assert(2 = 2 ^ 1) by go.
  rewrite H at 2; clear H.
  rewrite Z.ge_le_iff.
  apply Z.pow_le_mono_r_iff ; omega.
  - assert (Z.neg p < 0) by apply Zlt_neg_0 ; go.
Qed.

Lemma getCarryMonotone_neg : forall m, m < 0 -> m <= getCarry m.
Proof.
  intros m Hm.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 ; try omega.
  induction m.
  go.
  - assert (Z.pos p > 0) by apply Zgt_pos_0 ; go.
  - apply Zdiv_le_lower_bound.
    rewrite <- Z.gt_lt_iff ; apply pown0 ; assumption.
    rewrite Z.mul_comm.
    apply le_mul_neg ; try assumption.
    assert(Hnn:= pown n Hn).
    omega.
Qed.

Lemma getResidue_pos_str: forall m,
  0 < m < 2^n ->
  0 < getResidue m.
Proof.
  intros m Hm.
  unfold getResidue.
  rewrite Z.mod_small ; omega.
Qed.

Lemma getCarry_pos: forall m,
  0 <= m ->
  0 <= getCarry m.
Proof.
  intros m Hm.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 ; try omega.
  apply Z.div_pos.
  assumption.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
Qed.

Lemma getCarry_pos_str: forall m,
  2 ^ n <= m ->
  0 < getCarry m.
Proof.
  intros m Hm.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 ; try omega.
  apply Z.div_str_pos.
  split.
  rewrite <- Z.gt_lt_iff.
  apply pown0.
  assumption.
  assumption.
Qed.

Lemma getCarry_1: forall m,
  2^n <= m < 2^(n+1) ->
  getCarry m = 1.
Proof.
  intros m Hm.
  unfold getCarry.
  rewrite Z.shiftr_div_pow2 ; try omega.
  assert(1<= m / 2 ^ n).
  replace 1 with (2 ^ n/2 ^ n) by (apply Z_div_same_full; intro ; assert(Ht:= pown0 n Hn) ; omega).
  apply Z_div_le.
  apply pown0 ; auto.
  omega.
  assert(m / 2 ^ n < 2).
  apply Z.div_lt_upper_bound.
  assert(Hnn := pown0 n Hn) ; omega.
  rewrite Z.mul_comm.
  rewrite <- Z.pow_succ_r.
  destruct Hm.
  rewrite <- Z.add_1_r.
  assumption.
  omega.
  omega.
Qed.

End Integer.