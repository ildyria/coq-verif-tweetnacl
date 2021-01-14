Require Import compcert.common.Memory.
Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.msl.ageable.
Require Import VST.msl.age_to.
Require Import VST.veric.coqlib4.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.semax.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.age_to_resource_at.

Set Bullet Behavior "Strict Subproofs".

Ltac hered :=
  match goal with
    H : ?P ?x |- ?P ?y => revert H
  end;
  match goal with
    |- ?P ?x -> ?P ?y =>
    cut (hereditary age P);
    [ let h := fresh "h" in intros h; apply h; auto | ]
  end.

Ltac agejoinhyp :=
  match goal with
    H : sepalg.join _ _ ?m, A : age ?m _ |- _ =>
    pose proof age1_join2 _ H A; clear H
  end.

Ltac agehyps :=
  match goal with
    H : age ?x ?y, HH : ?P ?x |- _ =>
    cut (P y);
    [ clear HH; intros HH
    | hered;
      try apply pred_hered;
      try apply predicates_hered.exactly_obligation_1]
  end.

(** * Aging and predicates *)

Lemma hereditary_func_at' loc fs :
  hereditary age (seplog.func_at' fs loc).
Proof.
  apply pred_hered.
Qed.

Lemma anti_hereditary_func_at' loc fs :
  hereditary (fun x y => age y x) (seplog.func_at' fs loc).
Proof.
  intros x y a; destruct fs as [f cc A P Q]; simpl.
  intros [pp E].
  destruct (proj2 (age1_PURE _ _ loc (FUN f cc) a)) as [pp' Ey]; eauto.
  pose proof resource_at_approx y loc as H.
  rewrite Ey in H at 1; simpl in H.
  rewrite <-H.
  exists pp'.
  reflexivity.
Qed.

Lemma pures_eq_unage {phi1 phi1' phi2}:
  ge (level phi1') (level phi2) ->
  age phi1 phi1' ->
  juicy_safety.pures_eq phi1' phi2 ->
  juicy_safety.pures_eq phi1 phi2.
Proof.
  intros L A [S P]; split; intros loc; [clear P; autospec S | clear S; autospec P ].
  - rewrite (age_resource_at A) in S.
    destruct (phi1 @ loc) eqn:E; auto.
    simpl in S.
    rewrite S.
    rewrite preds_fmap_fmap.
    rewrite approx_oo_approx'; auto.
    rewrite approx'_oo_approx; auto.
  - destruct (phi2 @ loc) eqn:E; auto.
    revert P.
    eapply age1_PURE. auto.
Qed.

(** * Aging and operational steps *)

Lemma jstep_age_sim {G C} {csem : @semantics.CoreSemantics G C mem} {ge c c' jm1 jm2 jm1'} :
  age jm1 jm2 ->
  jstep csem ge c jm1 c' jm1' ->
  level jm2 <> O ->
  exists jm2',
    age jm1' jm2' /\
    jstep csem ge c jm2 c' jm2'.
Proof.
  intros A [step [rd lev]] nz.
  destruct (age1 jm1') as [jm2'|] eqn:E.
  - exists jm2'. split; auto.
    split; [|split]; auto.
    + exact_eq step.
      f_equal; apply age_jm_dry; auto.
    + eapply (age_resource_decay _ (m_phi jm1) (m_phi jm1')).
      * exact_eq rd.
        f_equal. f_equal. apply age_jm_dry; auto.
      * apply age_jm_phi; auto.
      * apply age_jm_phi; auto.
      * rewrite level_juice_level_phi in *. auto.
    + apply age_level in E.
      apply age_level in A.
      omega.
  - apply age1_level0 in E.
    apply age_level in A.
    omega.
Qed.

Lemma jsafeN_age Z Jspec ge ora q n jm jmaged :
  ext_spec_stable age (JE_spec _ Jspec) ->
  age jm jmaged ->
  le n (level jmaged) ->
  @jsafeN Z Jspec ge n ora q jm ->
  @jsafeN Z Jspec ge n ora q jmaged.
Proof.
  intros heredspec A L Safe; revert jmaged A L.
  induction Safe as
      [ z c jm
      | n z c jm c' jm' step safe IH
      | n z c jm ef args x atex Pre Post
      | n z c jm v Halt Exit ]; intros jmaged A L.
  - constructor 1.
  - simpl in step.
    destruct (jstep_age_sim A step ltac:(omega)) as [jmaged' [A' step']].
    econstructor 2; eauto.
    apply IH; eauto.
    apply age_level in A'.
    apply age_level in A.
    destruct step as [_ [_ ?]].
    omega.
  - econstructor 3.
    + eauto.
    + eapply (proj1 heredspec); eauto.
    + intros ret jm' z' n' Hargsty Hretty H rel post.
      destruct (Post ret jm' z' n' Hargsty Hretty H) as (c' & atex' & safe'); eauto.
      unfold juicy_safety.Hrel in *.
      split;[|split]; try apply rel.
      * apply age_level in A; omega.
      * apply age_jm_phi in A.
        unshelve eapply (pures_eq_unage _ A), rel.
        do 2 rewrite <-level_juice_level_phi.
        omega.
  - econstructor 4. eauto.
    eapply (proj2 heredspec); eauto.
Qed.

Lemma jsafeN_age_to Z Jspec ge ora q n l jm :
  ext_spec_stable age (JE_spec _ Jspec) ->
  le n l ->
  @jsafeN Z Jspec ge n ora q jm ->
  @jsafeN Z Jspec ge n ora q (age_to l jm).
Proof.
  intros Stable nl.
  apply age_to_ind_refined.
  intros x y H L.
  apply jsafeN_age; auto.
  omega.
Qed.

Lemma m_dry_age_to n jm : m_dry (age_to n jm) = m_dry jm.
Proof.
  remember (m_dry jm) as m eqn:E; symmetry; revert E.
  apply age_to_ind; auto.
  intros x y H E ->. rewrite E; auto. clear E.
  apply age_jm_dry; auto.
Qed.

Lemma m_phi_age_to n jm : m_phi (age_to n jm) = age_to n (m_phi jm).
Proof.
  unfold age_to.
  rewrite level_juice_level_phi.
  generalize (level (m_phi jm) - n)%nat; clear n.
  intros n; induction n. reflexivity.
  simpl. rewrite <- IHn.
  clear IHn. generalize (age_by n jm); clear jm; intros jm.
  unfold age1'.
  destruct (age1 jm) as [jm'|] eqn:e.
  - rewrite (age1_juicy_mem_Some _ _ e). easy.
  - rewrite (age1_juicy_mem_None1 _ e). easy.
Qed.
