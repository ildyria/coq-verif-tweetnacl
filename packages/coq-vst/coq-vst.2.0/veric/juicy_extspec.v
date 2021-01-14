Require Import VST.veric.juicy_base.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.shares.
Require Import VST.veric.juicy_safety.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.initial_world.

Local Open Scope nat_scope.
Local Open Scope pred.

Record juicy_ext_spec (Z: Type) := {
  JE_spec:> external_specification juicy_mem external_function Z;
  JE_pre_hered: forall e t ge_s typs args z, hereditary age (ext_spec_pre JE_spec e t ge_s typs args z);
  JE_post_hered: forall e t ge_s tret rv z, hereditary age (ext_spec_post JE_spec e t ge_s tret rv z);
  JE_exit_hered: forall rv z, hereditary age (ext_spec_exit JE_spec rv z)
}.

Class OracleKind := {
  OK_ty : Type;
  OK_spec: juicy_ext_spec OK_ty
}.

Definition jstep {G C} (csem: @CoreSemantics G C mem)
  (ge: G)  (q: C) (jm: juicy_mem) (q': C) (jm': juicy_mem) : Prop :=
 corestep csem ge q (m_dry jm) q' (m_dry jm') /\
 resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm') /\
 level jm = S (level jm').

Definition j_halted {G C} (csem: @CoreSemantics G C mem)
       (c: C) : option val :=
     halted csem c.

Lemma jstep_not_at_external {G C} (csem: @CoreSemantics G C mem):
  forall ge m q m' q', jstep csem ge q m q' m' -> at_external csem q = None.
Proof.
  intros.
  destruct H. eapply corestep_not_at_external; eauto.
Qed.

Lemma jstep_not_halted  {G C} (csem: @CoreSemantics G C mem):
  forall ge m q m' q', jstep csem ge q m q' m' -> j_halted csem q = None.
Proof.
  intros. destruct H. eapply corestep_not_halted; eauto.
Qed.

Lemma j_at_external_halted_excl {G C} (csem: @CoreSemantics G C mem):
  forall (q : C),
  at_external csem q = None \/ j_halted csem q = None.
Proof.
 intros.
 destruct (at_external_halted_excl csem q); [left | right]; auto.
Qed.

Record jm_init_package: Type := {
  jminit_m: Memory.mem;
  jminit_prog: program;
  jminit_G: tycontext.funspecs;
  jminit_lev: nat;
  jminit_init_mem: Genv.init_mem jminit_prog = Some jminit_m;
  jminit_defs_no_dups:   list_norepet (prog_defs_names jminit_prog);
  jminit_fdecs_match: match_fdecs (prog_funct jminit_prog) jminit_G
}.

Definition init_jmem {G} (ge: G) (jm: juicy_mem) (d: jm_init_package) :=
  jm = initial_jm (jminit_prog d) (jminit_m d) (jminit_G d) (jminit_lev d)
         (jminit_init_mem d) (jminit_defs_no_dups d) (jminit_fdecs_match d).

Definition juicy_core_sem
  {G C} (csem: @CoreSemantics G C mem) :
   @CoreSemantics G C juicy_mem :=
  @Build_CoreSemantics _ _ _
    (semantics.initial_core csem)
    (at_external csem)
    (after_external csem)
    (j_halted csem)
    (jstep csem)
    (jstep_not_at_external csem)
    (jstep_not_halted csem)
    (j_at_external_halted_excl csem).

Section upd_exit.
  Context {Z : Type}.
  Variable spec : juicy_ext_spec Z.

  Definition upd_exit' (Q_exit : option val -> Z -> juicy_mem -> Prop) :=
  {| ext_spec_type := ext_spec_type spec
   ; ext_spec_pre := ext_spec_pre spec
   ; ext_spec_post := ext_spec_post spec
   ; ext_spec_exit := Q_exit |}.

  Definition upd_exit'' (ef : external_function) (x : ext_spec_type spec ef) ge :=
    upd_exit' (ext_spec_post spec ef x ge (sig_res (ef_sig ef))).

  Program Definition upd_exit {ef : external_function} (x : ext_spec_type spec ef) ge :=
    Build_juicy_ext_spec _ (upd_exit'' _ x ge) _ _ _.
  Next Obligation. intros. eapply JE_pre_hered; eauto. Qed.
  Next Obligation. intros. eapply JE_post_hered; eauto. Qed.
  Next Obligation. intros. eapply JE_post_hered; eauto. Qed.
End upd_exit.

Obligation Tactic := Tactics.program_simpl.

Program Definition juicy_mem_op (P : pred rmap) : pred juicy_mem :=
  fun jm => P (m_phi jm).
 Next Obligation.
  intro; intros.
  apply age1_juicy_mem_unpack in H.
  destruct H.
  eapply pred_hereditary; eauto.
 Qed.

Lemma age_resource_decay:
   forall b jm1 jm2 jm1' jm2',
        resource_decay b jm1 jm2 ->
        age jm1 jm1' -> age jm2 jm2' ->
        level jm1 = S (level jm2) ->
        resource_decay b jm1' jm2'.
Proof.
  unfold resource_decay; intros.
  rename H2 into LEV.
  destruct H as [H' H].
  split.
  Focus 1. {
    clear H.
    apply age_level in H0; apply age_level in H1.
    rewrite H0 in *; rewrite H1 in *. inv LEV. rewrite H2.
    clear. forget (level jm2') as n. omega.
  } Unfocus.
  intro l.
  specialize (H l).
  destruct H.
  split.
  Focus 1. {
    intro.
    specialize (H H3).
    erewrite <- necR_NO; eauto.  constructor 1; auto.
  } Unfocus.
  destruct H2 as [?|[?|[?|?]]].
  + left.
    clear H. unfold age in *.
    rewrite (age1_resource_at _ _ H0 l (jm1 @ l)); [ | symmetry; apply resource_at_approx].
    rewrite (age1_resource_at _ _ H1 l (jm2 @ l)); [ | symmetry; apply resource_at_approx].
    rewrite <- H2.
    rewrite resource_fmap_fmap.
    rewrite resource_fmap_fmap.
    f_equal.
    - change R.approx with approx.
      rewrite approx_oo_approx'; [rewrite approx_oo_approx'; auto |].
      * apply age_level in H0; apply age_level in H1.
        unfold rmap  in *;
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; omega.
      * apply age_level in H0; apply age_level in H1.
        unfold rmap in *.
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; omega.
    - change R.approx with approx.
      rewrite approx'_oo_approx; [rewrite approx'_oo_approx; auto |].
      * apply age_level in H0; apply age_level in H1.
        unfold rmap  in *;
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; omega.
      * apply age_level in H0; apply age_level in H1.
        unfold rmap in *.
        forget (level jm1) as j1. forget (level jm1') as j1'. forget (level jm2) as j2. forget (level jm2') as j2'.
        subst; omega.
  + right.
    destruct H2 as [sh [wsh [v [v' [? ?]]]]].
    left; exists sh, wsh, v,v'.
    split.
    - apply age_level in H1.
      unfold rmap in *.
      forget (@level R.rmap R.ag_rmap jm2) as j2.
      forget (@level R.rmap R.ag_rmap jm2') as j2'. subst j2.
      clear - H2 H0 LEV.
      revert H2; case_eq (jm1 @ l); intros; inv H2.
      pose proof (necR_YES jm1 jm1' l sh r (VAL v) p (rt_step _ _ _ _ H0) H).
      rewrite H1.
      simpl. rewrite preds_fmap_fmap.
      apply age_level in H0.
      rewrite approx_oo_approx'.
        2: rewrite H0 in *; inv LEV; omega.
      rewrite approx'_oo_approx.
        2: rewrite H0 in *; inv LEV; omega.
      f_equal. apply proof_irr.
      rewrite H5.
      rewrite <- (approx_oo_approx' j2' (S j2')) at 1 by auto.
      rewrite <- (approx'_oo_approx j2' (S j2')) at 2 by auto.
      rewrite <- preds_fmap_fmap; rewrite H5. rewrite preds_fmap_NoneP. auto. 
    - pose proof (age1_YES _ _ l sh (writable_readable_share wsh) (VAL v') H1).
      rewrite H4 in H3. auto.
  + destruct H2 as [? [v ?]]; right; right; left.
    split; auto. exists v.   apply (age1_YES _ _ l _ _ _ H1) in H3. auto.
  + right; right; right.
    destruct H2 as [v [pp [? ?]]]. exists v. econstructor; split; auto. 
    pose proof (age1_resource_at _ _ H0 l (YES Share.top readable_share_top(VAL v) pp)).
    rewrite H4.
    simpl. reflexivity.
    rewrite <- (resource_at_approx jm1 l).
    rewrite H2. reflexivity.
    assert (necR jm2 jm2'). apply laterR_necR. constructor. auto.
    apply (necR_NO _ _ l Share.bot bot_unreadable H4). auto.
Qed.

Lemma necR_PURE' phi0 phi k p adr :
  necR phi0 phi ->
  phi @ adr = PURE k p ->
  (*a stronger theorem is possible -- this one doesn't relate p, pp*)
  exists pp, phi0 @ adr = PURE k pp.
Proof.
  intros Hnec H.
  case_eq (phi0 @ adr). 
  { intros. eapply necR_NO in Hnec; try eassumption. 
    rewrite Hnec in H0. rewrite H0 in H. congruence. }
  { intros. eapply necR_YES in Hnec; eauto. rewrite Hnec in H. congruence. }
  { generalize (necR_level _ _ Hnec); intros Hlev.
    intros. eapply necR_PURE in Hnec; eauto.
    rewrite Hnec in H. inversion H. subst. eexists. eauto. }
Qed.

Lemma age_safe {G C}
  (csem: @CoreSemantics G C mem) {Z}
      (genv_symb: G -> PTree.t block) (Hspec : juicy_ext_spec Z):
  forall jm jm0, age jm0 jm ->
  forall ge ora c,
   safeN genv_symb (juicy_core_sem csem) Hspec ge (level jm0) ora c jm0 ->
   safeN genv_symb (juicy_core_sem csem) Hspec ge (level jm) ora c jm.
Proof.
  intros. rename H into H2.
   rewrite (age_level _ _ H2) in H0.
   remember (level jm) as N.
   revert c jm0 jm HeqN H2 H0; induction N; intros.
   constructor.
  remember (S N) as SN.
   subst SN.
  inv H0.
  + pose proof (age_level _ _ H2).
   destruct H1 as (?&?&?).
   assert (level m' > 0) by omega.
   assert (exists i, level m' = S i).
   destruct (level m'). omegaContradiction. eauto.
   destruct H6 as [i ?].
   apply levelS_age1 in H6. destruct H6 as [jm1' ].
   econstructor; eauto.
   split.
   replace (m_dry jm) with (m_dry jm0)
     by (decompose [and] (age1_juicy_mem_unpack _ _ H2); auto).
   instantiate (1 := jm1').
   replace (m_dry jm1') with (m_dry m')
     by (decompose [and] (age1_juicy_mem_unpack _ _ H6); auto).
   eauto.
   split.
   replace (m_dry jm) with (m_dry jm0)
     by (decompose [and] (age1_juicy_mem_unpack _ _ H2); auto).
   eapply age_resource_decay; try eassumption.
   destruct (age1_juicy_mem_unpack _ _ H2); auto.
   destruct (age1_juicy_mem_unpack _ _ H6); auto.
   apply age_level in H6. rewrite <- H6.
   omega.
   eapply IHN; try eassumption.
   apply age_level in H6; omega.
  + eapply safeN_external; [eauto | eapply JE_pre_hered; eauto |].
    intros.
    destruct (H4 ret m' z' n') as [c' [? ?]]; auto.
    - assert (level (m_phi jm) < level (m_phi jm0)).
      Focus 1. {
        apply age_level in H2.
        do 2 rewrite <-level_juice_level_phi.
        destruct H0.
        rewrite H2; omega.
      } Unfocus.
      destruct H0 as (?&?&?).
      split3; [auto | do 2 rewrite <-level_juice_level_phi in H6; omega |].
      split.
      * destruct H8 as [H8 _].
        unfold pures_sub in H8. intros adr. specialize (H8 adr).
        assert (Hage: age (m_phi jm0) (m_phi jm)) by (apply age_jm_phi; auto).
        case_eq (m_phi jm0 @ adr); auto.
        intros k p Hphi.
        apply age1_resource_at with (loc := adr) (r := PURE k p) in Hage; auto.
       ++ rewrite Hage in H8; rewrite  H8; simpl.
          f_equal. unfold preds_fmap. destruct p. f_equal.
          generalize (approx_oo_approx' (level m') (level jm)); intros H9.
          spec H9; [omega |].
          generalize (approx'_oo_approx (level m') (level jm)); intros H10.
          spec H10; [omega |].
          do 2 rewrite <-level_juice_level_phi.
          rewrite fmap_app.
          rewrite H9, H10; auto.
       ++ rewrite <-resource_at_approx, Hphi; auto.
      * intros adr. case_eq (m_phi m' @ adr); auto. intros k p Hm'.
        destruct H8 as [_ H8].
        spec H8 adr. rewrite Hm' in H8. destruct H8 as [pp H8].
        apply age_jm_phi in H2.
        assert (Hnec: necR (m_phi jm0) (m_phi jm)) by (apply rt_step; auto).
        eapply necR_PURE' in Hnec; eauto.
    - exists c'; split; auto.
  + unfold j_halted in *.
    eapply safeN_halted; eauto.
    eapply JE_exit_hered; eauto.
Qed.

Lemma juicy_core_sem_preserves_corestep_fun
  {G C} (csem: @CoreSemantics G C mem) :
  corestep_fun csem ->
  corestep_fun (juicy_core_sem csem).
Proof.
  intros determinism ge jm q jm1 q1 jm2 q2 step1 step2.
  destruct step1 as [step1 [[ll1 rd1] l1]].
  destruct step2 as [step2 [[ll2 rd2] l2]].
  pose proof determinism _ _ _ _ _ _ _ step1 step2 as E.
  injection E as <- E; f_equal.
  apply juicy_mem_ext; auto.
  assert (El: level jm1 = level jm2) by (clear -l1 l2; omega).
  apply rmap_ext. now do 2 rewrite <-level_juice_level_phi; auto.
  intros l.
  specialize (rd1 l); specialize (rd2 l).
  rewrite level_juice_level_phi in *.
  destruct jm  as [m  phi  jmc  jmacc  jmma  jmall ].
  destruct jm1 as [m1 phi1 jmc1 jmacc1 jmma1 jmall1].
  destruct jm2 as [m2 phi2 jmc2 jmacc2 jmma2 jmall2].
  simpl in *.
  subst m2; rename m1 into m'.
  destruct rd1 as [jmno [E1 | [[sh1 [rsh1 [v1 [v1' [E1 E1']]]]] | [[pos1 [v1 E1]] | [v1 [pp1 [E1 E1']]]]]]];
  destruct rd2 as [_    [E2 | [[sh2 [rsh2 [v2 [v2' [E2 E2']]]]] | [[pos2 [v2 E2]] | [v2 [pp2 [E2 E2']]]]]]];
  try pose proof jmno pos1 as phino; try pose proof (jmno pos2) as phino; clear jmno;
    remember (phi  @ l) as x ;
    remember (phi1 @ l) as x1;
    remember (phi2 @ l) as x2;
    subst.

  - (* phi1: same   | phi2: same   *)
    congruence.

  - (* phi1: same   | phi2: update *)
    rewrite <- E1, El.
    rewrite El in E1.
    rewrite E1 in E2.
    destruct (jmc1 _ _ _ _ _ E2).
    destruct (jmc2 _ _ _ _ _ E2').
    congruence.

  - (* phi1: same   | phi2: alloc  *)
    exfalso.
    rewrite phino in E1. simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc2 l).
    rewrite E2 in jmacc2.
    simpl in jmacc2.
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: same   | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite <- E1 in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    clear -jmacc2. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence. contradiction Share.nontrivial.
  - (* phi1: update | phi2: same   *)
    rewrite <- E2, <-El.
    rewrite <-El in E2.
    rewrite E2 in E1.
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E1).
    congruence.

  - (* phi1: update | phi2: update *)
    destruct (jmc1 _ _ _ _ _ E1').
    destruct (jmc2 _ _ _ _ _ E2').
    rewrite E1', E2'.
    destruct (phi@l); inv E1; inv E2.
    f_equal. apply proof_irr.
  - (* phi1: update | phi2: alloc  *)
    rewrite phino in E1.
    simpl in E1.
    inversion E1.

  - (* phi1: update | phi2: free   *)
    exfalso.
    rewrite E2 in E1.
    simpl in E1.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc1 in jmacc2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc2; try congruence.  
  - (* phi1: alloc  | phi2: same   *)
    exfalso.
    rewrite phino in E2. simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    specialize (jmacc1 l).
    rewrite E1 in jmacc1.
    simpl in jmacc1.
    rewrite jmacc2 in jmacc1.
    clear -jmacc1.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial. 
  - (* phi1: alloc  | phi2: update *)
    rewrite phino in E2.
    simpl in E2.
    inversion E2.

  - (* phi1: alloc  | phi2: alloc  *)
    destruct (jmc1 _ _ _ _ _ E1).
    destruct (jmc2 _ _ _ _ _ E2).
    congruence.

  - (* phi1: alloc  | phi2: free   *)
    congruence.

  - (* phi2: free   | phi2: same   *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite <- E2 in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1. exfalso.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence. contradiction Share.nontrivial.  
  - (* phi2: free   | phi2: update *)
    exfalso.
    rewrite E1 in E2.
    simpl in E2.
    specialize (jmacc2 l).
    rewrite E2' in jmacc2.
    simpl in jmacc2.
    specialize (jmacc1 l).
    rewrite E1' in jmacc1.
    simpl in jmacc1.
    destruct (Share.EqDec_share Share.bot Share.bot) as [_ | F]; [ | congruence].
    rewrite jmacc2 in jmacc1.
    clear -jmacc1 rsh2.
    unfold perm_of_sh in *.
    repeat if_tac in jmacc1; try congruence.
  - (* phi2: free   | phi2: alloc  *)
    congruence.

  - (* phi2: free   | phi2: free   *)
    congruence.
Qed.
