From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.
From stdpp Require Import list.
Require Import ssreflect.
Require Import Recdef.

Open Scope Z.

Definition subst_0xffff t := t - 65535.

Definition sub_step_1 (a:Z) (m t:list Z) : list Z :=
    let t' := nth (Z.to_nat a) t 0 in
      (upd_nth (Z.to_nat a) m (subst_0xffff t')).

Lemma sub_step_1_Zlength : forall a m t,
  0 <= a < Zlength m ->
  Zlength (sub_step_1 a m t) = Zlength m.
Proof.
  intros a m t Ham.
  rewrite /sub_step_1.
  rewrite ?upd_nth_Zlength.
  reflexivity.
  all: rewrite ?Z2Nat.id.
  all: omega.
Qed.

Local Lemma sub_fn_rev_s_sub_step_1_ind_Zlength : forall a m t,
  0 <= a < Zlength m ->
  Zlength (sub_fn_rev 1 sub_step_1 a m t) = Zlength m ->
  Zlength (sub_fn_rev 1 sub_step_1 (a+1) m t) = Zlength m.
Proof.
  intros i m t Ham Hind.
  rewrite sub_fn_rev_equation.
  flatten.
  replace ( i + 1 - 1) with i by omega.
  rewrite <- Hind.
  apply sub_step_1_Zlength.
  rewrite Hind.
  assumption.
Qed.

Lemma sub_fn_rev_s_sub_step_1_Zlength : forall a m t,
  0 < a < 16 ->
  Zlength m = 16 ->
  Zlength (sub_fn_rev 1 sub_step_1 a m t) = Zlength m.
Proof.
  intros.
  pattern a.
  destruct a.
  all: try reflexivity.
  revert H.
  induction p using Pos.peano_ind.
  by rewrite sub_fn_rev_1.
  intros.
  replace ((Z.pos (Pos.succ p))) with (Z.pos p + 1) by lia.
  apply sub_fn_rev_s_sub_step_1_ind_Zlength.
  2: apply IHp.
  lia.
  lia.
Qed.

Local Lemma sub_fn_rev_s_sub_step_1_ind_bound : forall a m t,
  0 < a < 16 ->
  Zlength m = 16 ->
  Forall (fun x => 0 <= x < 2 ^ 16) t ->
  Forall (fun x => -2^16 < x < 2^16) (take (Z.to_nat a) (sub_fn_rev 1 sub_step_1 a m t)) ->
  Forall (fun x => -2^16 < x < 2^16) (take (Z.to_nat (a + 1)) (sub_fn_rev 1 sub_step_1 (a + 1) m t)).
Proof.
  intros i m t Ham Hm Hbm Hind.
  rewrite sub_fn_rev_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega.
  replace ( i + 1 - 1) with i by omega.
  rewrite -(take_cons_Zlength _ _ 0).
  2: rewrite sub_step_1_Zlength sub_fn_rev_s_sub_step_1_Zlength; omega.
  remember (sub_fn_rev 1 sub_step_1 i m t) as m'.
  apply Forall_app_2.
  rewrite /sub_step_1.
  rewrite (upd_nth_alter _ (fun x => (subst_0xffff (nth (Z.to_nat i) t 0)))).
  rewrite take_alter.
  2: reflexivity.
  3: reflexivity.
  assumption.
  3: apply Forall_cons_2.
  4: apply Forall_nil ; trivial.
  3: rewrite /sub_step_1;
  rewrite upd_nth_same_Zlength /subst_0xffff.
  3: assert(- 2 ^ 16 + 1 + 65535 ≤ nth (Z.to_nat i) t 0 ∧ nth (Z.to_nat i) t 0 < 1 + 65535) by
    (change(- 2 ^ 16 + 1 + 65535) with 0 ; change(1 + 65535) with (2^16);
    apply Forall_nth_d; [compute ; split; go|assumption]).
  all: try omega.
  apply Nat2Z.inj_lt.
  rewrite -Zlength_correct.
  all: rewrite ?Z2Nat.id ?Heqm' ?sub_fn_rev_s_sub_step_1_Zlength.
  all: try omega.
Qed.

Lemma sub_fn_rev_s_sub_step_1_bound : forall i m t,
  Zlength m = 16 ->
  0 < i < Zlength m ->
  Forall (fun x => 0 <= x < 2 ^ 16) t ->
  Forall (λ a : ℤ, - 2 ^ 16 < a ∧ a < 2^16) (take (Z.to_nat 1) m) ->
  Forall (fun x => -2^16 < x < 2^16) (take (Z.to_nat i) (sub_fn_rev 1 sub_step_1 i m t)).
Proof.
intros.
pattern i.
apply P016_impl ; try omega.
rewrite sub_fn_rev_1; assumption.
intros ; apply sub_fn_rev_s_sub_step_1_ind_bound ; try omega ; try assumption.
Qed.

Close Scope Z.