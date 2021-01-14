Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.aging_lemmas.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.coqlib5.
Require Import VST.concurrency.semax_conc_pred.
Require Import VST.concurrency.semax_conc.
Require Import VST.concurrency.juicy_machine.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.addressFiniteMap.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.JuicyMachineModule.
Require Import VST.concurrency.sync_preds_defs.
Require Import VST.concurrency.sync_preds.
Require Import VST.concurrency.join_lemmas.
Require Import VST.concurrency.cl_step_lemmas.
Require Import VST.concurrency.resource_decay_lemmas.
Require Import VST.concurrency.resource_decay_join.
Require Import VST.concurrency.semax_invariant.
Require Import VST.concurrency.sync_preds.
Require Import VST.concurrency.semax_initial.
Require Import VST.concurrency.semax_progress.
Require Import VST.concurrency.semax_preservation_jspec.
Require Import VST.concurrency.semax_safety_makelock.
Require Import VST.concurrency.semax_safety_spawn.
Require Import VST.concurrency.semax_safety_release.
Require Import VST.concurrency.semax_safety_freelock.
Require Import VST.concurrency.semax_preservation.

Set Bullet Behavior "Strict Subproofs".

Inductive jmsafe : nat -> cm_state -> Prop :=
| jmsafe_0 m ge sch tp : jmsafe 0 (m, ge, (sch, tp))
| jmsafe_halted n m ge tp : jmsafe n (m, ge, (nil, tp))
| jmsafe_core n m m' ge sch tp tp':
    @JuicyMachine.machine_step ge sch nil tp m sch nil tp' m' ->
    jmsafe n (m', ge, (sch, tp')) ->
    jmsafe (S n) (m, ge, (sch, tp))
| jmsafe_sch n m m' ge i sch tp tp':
    @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m' ->
    (forall sch', jmsafe n (m', ge, (sch', tp'))) ->
    jmsafe (S n) (m, ge, (i :: sch, tp)).

(*
Inductive jmsafe : nat -> cm_state -> Prop :=
| jmsafe_0 m ge sch tp : jmsafe 0 (m, ge, (sch, tp))
| jmsafe_halted n m ge tp : jmsafe n (m, ge, (nil, tp))
| jmsafe_sch n m m' ge i sch tp tp':
    @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m' ->
    (forall sch', unique_Krun tp sch' -> jmsafe n (m', ge, (sch', tp'))) ->
    jmsafe (S n) (m, ge, (i :: sch, tp)).
 *)

Lemma step_sch_irr ge i sch sch' tp m tp' m' :
  @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m' ->
  @JuicyMachine.machine_step ge (i :: sch') nil tp m sch' nil tp' m'.
Proof.
  intros step.
  assert (i :: sch <> sch) by (clear; induction sch; congruence).
  inversion step; try solve [exfalso; eauto].
  - now eapply JuicyMachine.suspend_step; eauto.
  - now eapply JuicyMachine.sync_step; eauto.
  - now eapply JuicyMachine.halted_step; eauto.
  - now eapply JuicyMachine.schedfail; eauto.
Qed.

Require Import VST.concurrency.semax_simlemmas.

Lemma schstep_norun ge i sch tp m tp' m' :
  @JuicyMachine.machine_step ge (i :: sch) nil tp m sch nil tp' m' ->
  unique_Krun tp (i :: sch) ->
  1 < pos.n (num_threads tp') ->
  no_Krun tp'.
Proof.
  intros step uniq more.
  assert (i :: sch <> sch) by (clear; induction sch; congruence).
  assert (D: forall i j, containsThread tp i -> containsThread tp j -> i <> j -> 1 < pos.n tp.(num_threads)).
  { clear. intros; eapply (different_threads_means_several_threads i j); eauto. }
  assert (forall j cntj q, containsThread tp i -> i <> j -> @getThreadC j tp cntj <> @Krun code q).
  { intros j cntj q cnti ne E. autospec uniq. spec uniq j cntj q E. breakhyps. }

  inversion step; try tauto.
  all: try inversion Htstep; repeat match goal with H : ?x = ?y |- _ => subst x || subst y end.
  all: intros j cnti q.
  Set Printing Implicit.
  all: assert (tid = i) by (simpl in *; congruence); subst tid.
  all: destruct (eq_dec i j).
  all: try subst j.

  all: try (assert (cnti = Htid) by apply proof_irr; subst Htid).
  all: try (assert (ctn = cnti) by apply proof_irr; subst cnt).
  all: try (unshelve erewrite <-gtc_age; eauto).
  all: try (unshelve erewrite gLockSetCode; eauto).
  all: try (unshelve erewrite gRemLockSetCode; eauto).
  all: try (rewrite gssThreadCode; congruence).
  all: try (rewrite gssThreadCC; congruence).
  all: try (unshelve erewrite gsoThreadCode; eauto).
  all: try (unshelve erewrite <-gsoThreadCC; eauto).

  pose proof cnti as cnti_.
  apply cnt_age in cnti_.
  destruct (@cntAdd' _ _ _ _ _ cnti_) as [(cnti', ne) | Ei].
  unshelve erewrite gsoAddCode; eauto.
  rewrite gssThreadCode; congruence.
  rewrite gssAddCode. congruence. apply Ei.

  pose proof cnti as cnti_.
  apply cnt_age in cnti_.
  destruct (@cntAdd' _ _ _ _ _ cnti_) as [(cnti', ne) | Ei].
  unshelve erewrite gsoAddCode; eauto.
  unshelve erewrite gsoThreadCode; eauto.
  rewrite gssAddCode. congruence. apply Ei.

  all: try congruence.
  all: eauto.

  inversion Hhalted.
  unfold SEM.Sem in *.
  rewrite SEM.CLN_msem in Hcant.
  simpl in Hcant.
  inversion Hcant.

  intros E.
  hnf in uniq.
  autospec uniq.
  spec uniq j cnti q E. breakhyps.
Qed.

(*+ Final instantiation *)

Section Safety.
  Variables
    (CS : compspecs)
    (V : varspecs)
    (G : funspecs)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
    (prog : Clight.program)
    (all_safe : semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog V G)
    (init_mem_not_none : Genv.init_mem prog <> None).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).

  (* another, looser invariant to have more standard preservation
  statement *)
  Definition inv Gamma n state :=
    exists m, n <= m /\ state_invariant Jspec' Gamma m state.

  Lemma inv_sch_irr Gamma n m ge i sch sch' tp :
    inv Gamma n (m, ge, (i :: sch, tp)) ->
    inv Gamma n (m, ge, (i :: sch', tp)).
  Proof.
    intros (k & lkm & Hk).
    exists k; split; auto.
    eapply state_invariant_sch_irr, Hk.
  Qed.

  Lemma no_Krun_inv Gamma n m ge sch sch' tp :
    (1 < pos.n (num_threads tp) -> no_Krun tp) ->
    inv Gamma n (m, ge, (sch, tp)) ->
    inv Gamma n (m, ge, (sch', tp)).
  Proof.
    intros nokrun.
    intros (x & lx & i).
    exists x; split; auto.
    inversion i as [m0 ge0 sch0 tp0 PHI mcompat lev gamma lock_sparse lock_coh safety wellformed uniqkrun H0]; subst.
    esplit; eauto.
    intros H. autospec nokrun. revert H.
    apply no_Krun_unique_Krun, nokrun.
  Qed.

  Lemma blocked_at_external_dec state ef : {blocked_at_external state ef} + {~blocked_at_external state ef}.
  Proof.
    Local Ltac t := solve [right; intros []; intros; breakhyps].
    Ltac t' i cnti :=
      right; intros [i']; intros [cnti']; intros ?; breakhyps;
      try (assert (i' = i) by congruence; subst i');
      try (assert (cnti' = cnti) by apply proof_irr; subst cnti');
      breakhyps.

    destruct state as ((m, ge) & [ | i sch] & tp). now t.
    simpl.
    destruct (containsThread_dec i tp) as [cnti | ncnti]. 2: now t.
    destruct (@getThreadC i tp cnti) as [c | c | c v | v v0] eqn:Ei;
    try solve [right; intros [i' [cnti' [sch' [c0 [? [H [? ?]]]]]]]; inv H; proof_irr; congruence].
    destruct (cl_at_external c) as [(ef', args) | ] eqn:Eo;
    try solve [right; intros [i' [cnti' [sch' [c0 [? [H [? ?]]]]]]]; inv H; proof_irr; congruence].
    destruct (eq_dec ef ef'); try subst ef';
    try solve [right; intros [i' [cnti' [sch' [c0 [? [H [? ?]]]]]]]; inv H; proof_irr; congruence].
    (* destruct (EqDec_external_function ef ef'). subst ef'. 2: now t' i cnti. *)
    now left; repeat eexists; eauto.
  Qed.

  Theorem safety_induction Gamma n state :
    state_invariant Jspec' Gamma (S n) state ->
    exists state',
      state_step state state' /\
      (state_invariant Jspec' Gamma n state' \/
       state_invariant Jspec' Gamma (S n) state').
  Proof.
    intros inv.

    (* the case for makelock *)
    destruct (blocked_at_external_dec state MKLOCK) as [ismakelock|isnotmakelock].
    {
      apply safety_induction_makelock; eauto.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    (* the case for freelock *)
    destruct (blocked_at_external_dec state FREE_LOCK) as [isfreelock|isnotfreelock].
    {
      apply safety_induction_freelock; eauto.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    (* the case for spawn *)
    destruct (blocked_at_external_dec state CREATE) as [isspawn|isnotspawn].
    {
      apply safety_induction_spawn; eauto.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    (* the case for release *)
    destruct (blocked_at_external_dec state UNLOCK) as [isrelease|isnotrelease].
    {
      apply safety_induction_release; eauto.
      - hnf. apply Jspec'_juicy_mem_equiv.
      - hnf. apply Jspec'_hered.
      - apply personal_mem_equiv_spec.
    }

    destruct (progress CS ext_link ext_link_inj _ _ _ isnotspawn inv) as (state', step).
    exists state'; split; [ now apply step | ].
    eapply preservation; eauto.
  Qed.

  Lemma inv_step Gamma n state :
    inv Gamma (S n) state ->
    exists state',
      state_step state state' /\
      inv Gamma n state'.
  Proof.
    intros (m & lm & i).
    replace m with (S (m - 1)) in i by omega.
    destruct (safety_induction _ _ _ i) as (state' & step & inv').
    exists state'; split; [ now apply step | ].
    hnf. destruct inv'.
    - exists (m - 1). split. omega. assumption.
    - exists m. split. omega. exact_eq H; f_equal. omega.
  Qed.

  Lemma invariant_safe Gamma n state :
    inv Gamma n state -> jmsafe n state.
  Proof.
    intros INV.
    pose proof (inv_step) as Step.
    revert state INV.
    induction n; intros ((m, ge), (sch, tp)) INV.
    - apply jmsafe_0.
    - destruct sch.
      + apply jmsafe_halted.
      + destruct (Step _ _ _ INV) as (state' & step & INV').
        inversion step as [ | ge' m0 m' sch' sch'' tp0 tp' jmstep ]; subst; simpl in *.
        inversion jmstep; subst.
        all: try solve [ eapply jmsafe_core; eauto ].
        all: eapply jmsafe_sch; eauto.
        all: intros sch'; apply IHn.
        all: simpl in *.
        all: apply no_Krun_inv with (sch := sch); eauto.
        all: eapply schstep_norun; eauto.
        all: destruct INV as (? & lm & INV).
        all: inv INV; auto.
  Qed.

  Definition init_mem : { m | Genv.init_mem prog = Some m } := init_m prog init_mem_not_none.

  Definition spr :=
    semax_prog_rule
      (Concurrent_Espec unit CS ext_link) V G prog
      (proj1_sig init_mem) 0 all_safe (proj2_sig init_mem).

  Definition initial_corestate : corestate := projT1 (projT2 spr).

  Definition initial_jm (n : nat) : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n).

  Definition initial_machine_state (n : nat) :=
    ThreadPool.mk
      (pos.mkPos (le_n 1))
      (fun _ => Krun initial_corestate)
      (fun _ => m_phi (initial_jm n))
      (addressFiniteMap.AMap.empty _).

  Definition NoExternal_Espec : external_specification mem external_function unit :=
    Build_external_specification
      _ _ _
      (* no external calls from the machine *)
      (fun _ => False)
      (fun _ _ _ _ _ _ _ => False)
      (fun _ _ _ _ _ _ _ => False)
      (* when the machine is halted, it means no more schedule, there
      is nothing to check: *)
      (fun _ _ _ => Logic.True).

  Definition NoExternal_Hrel : nat -> mem -> mem -> Prop := fun _ _ _ => False.

  (* We state the theorem in terms of [safeN_] but because there are
  no external, this really just says that the initial state is
  "angelically safe" : for every schedule and every fuel n, there is a
  path either ending on an empty schedule or consuming all the
  fuel. *)

  Theorem safe_initial_state : forall sch r n genv_symb,
      safeN_
        (G := genv)
        (C := schedule * list _ * ThreadPool.t)
        (M := mem)
        (Z := unit)
        (genv_symb := genv_symb)
        (Hrel := NoExternal_Hrel)
        (JuicyMachine.MachineSemantics sch r)
        NoExternal_Espec
        (globalenv prog)
        n
        tt
        (sch, nil, initial_machine_state n)
        (proj1_sig init_mem).
  Proof.
    intros sch r n thisfunction.
    pose proof initial_invariant CS V G ext_link prog as INIT.
    repeat (specialize (INIT ltac:(assumption))).
    match type of INIT with
      _ _ ?a n ?b =>
      assert (init : inv a n b) by (hnf; eauto)
    end.
    pose proof inv_step as SIM.
    clear INIT; revert init.
    unfold initial_state, initial_machine_state.
    unfold initial_corestate, initial_jm, spr, init_mem.
    match goal with |- context[(sch, ?tp)] => generalize tp end.
    match goal with |- context[(proj1_sig ?m)] => generalize (proj1_sig m) end.
    (* here we decorelate the CoreSemantics parameters from the
    initial state parameters *)
    generalize sch at 2.
    generalize (globalenv prog), sch.
    clear -SIM.
    induction n; intros g sch schSEM m t INV; [ now constructor | ].
    destruct (SIM _ _ _ INV) as [cm' [step INV']].
    inversion step as [ | ? ? m' ? sch' ? tp' STEP ]; subst; clear step.
    - (* empty schedule *)
      eapply safeN_halted.
      + reflexivity.
      + apply I.
    - (* a step can be taken *)
      eapply safeN_step with (c' := (sch', nil, tp')) (m'0 := m').
      + eapply STEP.
      + apply IHn.
        apply INV'.
  Qed.

  (* The following is a slightly stronger result, proving [jmsafe]
  i.e. a safety that universally quantifies over all schedule each
  time a part of the schedule is consumed *)

  Theorem jmsafe_initial_state sch n :
    jmsafe n ((proj1_sig init_mem, globalenv prog), (sch, initial_machine_state n)).
  Proof.
    eapply invariant_safe.
    exists n; split; auto; apply initial_invariant.
  Qed.

  Lemma jmsafe_csafe n m ge sch s : jmsafe n (m, ge, (sch, s)) -> JuicyMachine.csafe ge (sch, nil, s) m n.
  Proof.
    clear.
    revert m ge sch s; induction n; intros m ge sch s SAFE.
    now constructor 1.
    inversion SAFE; subst.
    - constructor 2. reflexivity.
    - econstructor 3; simpl; eauto.
    - econstructor 4; simpl; eauto.
  Qed.

  (* [jmsafe] is an intermediate result, we can probably prove [csafe]
  directly *)

  Theorem safety_initial_state (sch : schedule) (n : nat) :
    JuicyMachine.csafe (globalenv prog) (sch, nil, initial_machine_state n) (proj1_sig init_mem) n.
  Proof.
    apply jmsafe_csafe, jmsafe_initial_state.
  Qed.

End Safety.
