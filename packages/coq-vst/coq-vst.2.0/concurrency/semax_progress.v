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
Require Import VST.msl.age_to.
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
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.shares.
Require Import VST.veric.age_to_resource_at.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.field_at.
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
Require Import VST.concurrency.semax_simlemmas.
Require Import VST.concurrency.rmap_locking.
Require Import VST.concurrency.lksize.

Set Bullet Behavior "Strict Subproofs".

Import Mem.

Lemma load_at_phi_restrict i tp (cnti : containsThread tp i) m
      (compat : mem_compatible tp m) b ofs v sh R phi0 o :
  join_sub phi0 (getThreadR cnti) ->
  (LKspec LKSIZE R sh (b, ofs)) phi0 ->
  (* typically given by lock_coherence: *)
  AMap.find (elt:=option rmap) (b, ofs) (lset tp) = Some o ->
  load Mint32 (restrPermMap (mem_compatible_locks_ltwritable compat)) b ofs = Some v ->
  load Mint32 (@juicyRestrict_locks _ m (mem_compat_thread_max_cohere compat cnti)) b ofs = Some v.
Proof.
  intros (phi1, j) lk found.
  unfold juicyRestrict_locks in *.
  Transparent Mem.load.
  unfold Mem.load. simpl.
  match goal with
    |- (if _ ?m ?c _ _ ?r then _ else _) =_ ->
      (if _ ?m' _ _ _ _ then _ else _) = _ =>
    cut (valid_access m c b ofs r =
         valid_access m' c b ofs r) end.
  { intros E. if_tac [va|nva]; if_tac [va'|nva']; auto; exfalso; congruence. }
  unfold valid_access in *.
  f_equal.
  unfold range_perm in *.
  extensionality ofs'.
  extensionality r.
  unfold perm in *.
  pose proof restrPermMap_Cur as RR.
  unfold permission_at in *.
  rewrite RR.
  rewrite RR.
  unfold lockSet in *.

  assert (notnone : (snd (mem_access m)) ! b <> None). {
    destruct compat as (Phi & [_ _ W _ _]).
    spec W b ofs. unfold lockGuts in *. cleanup.
    unfold block in *.
    rewrite found in W.
    autospec W. spec W ofs.
    spec W. now split; simpl; auto; lkomega.
    unfold "!!" in W. destruct ((snd (mem_access m)) ! b). congruence.
    pose proof Max_isCanonical m as can. hnf in can. apply equal_f with (x := ofs) in can.
    unfold getMaxPerm in *.
    simpl in *.
    rewrite can in W.
    inv W.
  }

  match goal with |- ?P = ?Q => cut (P /\ Q) end.
  { intros (?, ?). apply prop_ext; split; auto. }
  split.
  - erewrite A2PMap_found; eauto.
    constructor.
  - unfold juice2Perm_locks in *.
    unfold mapmap in *.
    unfold getCurPerm in *.
    unfold "!!".
    simpl.
    rewrite PTree.gmap.
    unfold option_map.
    rewrite PTree.gmap1.
    unfold option_map.
    simpl.
    destruct ((snd (mem_access m)) ! b) eqn:E. 2:tauto. clear notnone.
    unfold perm_of_res_lock in *.
    spec lk (b, ofs'). simpl in lk.
    if_tac [r'|nr] in lk. 2:now destruct nr; split; auto; lkomega.
    apply resource_at_join with (loc := (b, ofs')) in j.
    if_tac [e|ne] in lk.
    + destruct lk as (p & E0). rewrite E0 in j. inv j.
      * unfold block in *.
        rewr (getThreadR cnti @ (b, ofs')).
        simpl.
        unfold perm_of_sh.
        pose proof (readable_glb rsh3).
        repeat if_tac; try constructor; tauto.
      * unfold block in *.
        rewr (getThreadR cnti @ (b, ofs')).
        simpl.
        unfold perm_of_sh.
        pose proof (readable_glb rsh3).
        repeat if_tac; try constructor; tauto.
    + destruct lk as (p & E0). rewrite E0 in j. inv j.
      * unfold block in *.
        rewr (getThreadR cnti @ (b, ofs')).
        simpl.
        unfold perm_of_sh.
        pose proof (readable_glb rsh3).
        repeat if_tac; try constructor; tauto.
      * unfold block in *.
        rewr (getThreadR cnti @ (b, ofs')).
        simpl.
        unfold perm_of_sh.
        pose proof (readable_glb rsh3).
        repeat if_tac; try constructor; tauto.
Qed.

Lemma valid_access_restrPermMap m i tp Phi b ofs ophi
  (compat : mem_compatible_with tp m Phi)
  (lock_coh : lock_coherence' tp Phi m compat)
  (cnti : containsThread tp i)
  (Efind : AMap.find (elt:=option rmap) (b, Int.unsigned ofs) (lset tp) = Some ophi)
  (align : (4 | snd (b, Int.unsigned ofs)))
  (Hlt' : permMapLt
           (setPermBlock (Some Writable) b (Int.intval ofs) (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat)
           (getMaxPerm m)) :
  valid_access (restrPermMap Hlt') Mint32 b (Int.intval ofs) Writable.
Proof.
  split. 2:exact align.
  intros ofs' r.
  unfold perm in *.
  pose proof restrPermMap_Cur as RR.
  unfold permission_at in *.
  rewrite RR.
  simpl.
  pose proof compat.(loc_writable) as LW.
  spec LW b (Int.unsigned ofs). cleanup. rewrite Efind in LW. autospec LW. spec LW ofs'.
  rewrite !setPerm_spec.
  repeat (if_tac; [constructor |]).
  exfalso.
  simpl in r.
  assert (A : forall z, (b, z) <> (b, ofs') -> z <> ofs') by congruence.
  repeat match goal with H: (_,_)<>(_,_) |- _ => apply A in H end.
  omega.
Qed.

Lemma permMapLt_local_locks m i tp Phi b ofs ophi
      (compat : mem_compatible_with tp m Phi)
      (cnti : containsThread tp i)
      (Efind : AMap.find (elt:=option rmap) (b, Int.unsigned ofs) (lset tp) = Some ophi) :
  permMapLt
    (setPermBlock (Some Writable) b (Int.intval ofs)
                  (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat)
    (getMaxPerm m).
Proof.
  simpl.
  intros b' ofs'.
  assert (RR: (getMaxPerm m) !! b' ofs' = (mem_access m) !! b' ofs' Max)
    by (unfold getMaxPerm in *; rewrite PMap.gmap; reflexivity).

  pose proof compat.(loc_writable) as LW.
  spec LW b (Int.unsigned ofs). cleanup. rewrite Efind in LW. autospec LW. spec LW ofs'.
  rewrite RR.
  rewrite !setPerm_spec.
 repeat (
  if_tac; [match goal with H: (_,_) = (_,_) |-_ => inv H; apply LW; split; simpl; unfold Int.unsigned in *; lkomega end | ]).
 rewrite <-RR.
  apply juice2Perm_locks_cohere, mem_compat_thread_max_cohere.
  eexists; eauto.
Qed.

Lemma isLK_rewrite r :
  (forall (sh : Share.t) (rsh: readable_share sh) (z : Z) (P : preds), r <> YES sh rsh (LK z) P)
  <->
  ~ isLK r.
Proof.
  destruct r as [t0 | t0 p [] p0 | k p]; simpl; unfold isLK in *; split.
  all: try intros H ?; intros; breakhyps.
  intros E; injection E; intros; subst.
  apply H; eauto.
Qed.

Section Progress.
  Variables
    (CS : compspecs)
    (ext_link : string -> ident)
    (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2).

  Definition Jspec' := (@OK_spec (Concurrent_Espec unit CS ext_link)).

  Open Scope string_scope.

  Theorem progress Gamma n state :
    ~ blocked_at_external state CREATE ->
    state_invariant Jspec' Gamma (S n) state ->
    exists state',
      state_step state state'.
  Proof.
    intros not_spawn I.
    inversion I as [m ge sch tp Phi En envcoh compat sparse lock_coh safety wellformed unique E]. rewrite <-E in *.
    destruct sch as [ | i sch ].

    (* empty schedule: we loop in the same state *)
    {
      exists state. subst. constructor.
    }

    destruct (ssrnat.leq (S i) tp.(ThreadPool.num_threads).(pos.n)) eqn:Ei; swap 1 2.

    (* bad schedule *)
    {
      eexists.
      (* split. *)
      (* -  *)constructor.
        apply JuicyMachine.schedfail with i.
        + reflexivity.
        + unfold ThreadPool.containsThread.
          now rewrite Ei; auto.
        + constructor.
        + reflexivity.
    }

    (* the schedule selected one thread *)
    assert (cnti : ThreadPool.containsThread tp i) by apply Ei.
    remember (ThreadPool.getThreadC cnti) as ci eqn:Eci; symmetry in Eci.

    destruct ci as
        [ (* Krun *) ci
        | (* Kblocked *) ci
        | (* Kresume *) ci v
        | (* Kinit *) v1 v2 ].

    (* thread[i] is running *)
    {
      pose (jmi := jm_ cnti compat).
      (* pose (phii := m_phi jmi). *)
      (* pose (mi := m_dry jmi). *)

      destruct ci as [ve te k | ef args lid ve te k] eqn:Heqc.

      (* thread[i] is running and some internal step *)
      {
        (* get the next step of this particular thread (with safety for all oracles) *)
        assert (next: exists ci' jmi',
                   corestep (juicy_core_sem cl_core_sem) ge ci jmi ci' jmi'
                   /\ forall ora, jsafeN Jspec' ge n ora ci' jmi').
        {
          specialize (safety i cnti).
          pose proof (safety tt) as safei.
          rewrite Eci in *.
          inversion safei as [ | ? ? ? ? c' m' step safe H H2 H3 H4 | | ]; subst.
          2: now match goal with H : at_external _ _ = _ |- _ => inversion H end.
          2: now match goal with H : halted _ _ = _ |- _ => inversion H end.
          exists c', m'. split; [ apply step | ].
          revert step safety safe; clear.
          generalize (jm_ cnti compat).
          generalize (State ve te k).
          unfold jsafeN.
          intros c j step safety safe ora.
          eapply safe_corestep_forward.
          - apply juicy_core_sem_preserves_corestep_fun.
            apply semax_lemmas.cl_corestep_fun'.
          - apply step.
          - apply safety.
        }

        destruct next as (ci' & jmi' & stepi & safei').
        pose (tp' := age_tp_to (level jmi') tp).
        pose (tp'' := @ThreadPool.updThread i tp' (cnt_age' cnti) (Krun ci') (m_phi jmi')).
        pose (cm' := (m_dry jmi', ge, (i :: sch, tp''))).
        exists cm'.
        apply state_step_c; [].
        apply JuicyMachine.thread_step with
        (tid := i)
          (ev := nil)
          (Htid := cnti)
          (Hcmpt := mem_compatible_forget compat); [|]. reflexivity.
        eapply step_juicy; [ | | | | | ].
        + reflexivity.
        + now constructor.
        + exact Eci.
        + destruct stepi as [stepi decay].
          split.
          * simpl.
            subst.
            unfold SEM.Sem in *.
            rewrite SEM.CLN_msem.
            apply stepi.
          * simpl.
            exact_eq decay.
            reflexivity.
        + reflexivity.
        + reflexivity.
      }
      (* end of internal step *)

      (* thread[i] is running and about to call an external: Krun (at_ex c) -> Kblocked c *)
      {
        eexists.
        (* taking the step *)
        constructor.
        eapply JuicyMachine.suspend_step.
        + reflexivity.
        + reflexivity.
        + eapply mem_compatible_forget; eauto.
        + econstructor.
          * eassumption.
          * unfold SEM.Sem in *.
            rewrite SEM.CLN_msem.
            reflexivity.
          * constructor.
          * reflexivity.
      } (* end of Krun (at_ex c) -> Kblocked c *)
    } (* end of Krun *)

    (* thread[i] is in Kblocked *)
    {
      (* goes to Kresume ci' according to the rules of syncStep  *)

      destruct ci as [ve te k | ef args lid ve te k] eqn:Heqc.

      (* internal step: impossible, because in state Kblocked *)
      {
        exfalso.
        pose proof (wellformed i cnti) as W.
        rewrite Eci in W.
        apply W; auto.
      }
      (* back to external step *)

      (* paragraph below: ef has to be an EF_external *)
      assert (Hef : match ef with EF_external _ _ => Logic.True | _ => False end).
      {
        pose proof (safety i cnti tt) as safe_i.
        rewrite Eci in safe_i.
        fixsafe safe_i.
        inversion safe_i; subst; [ now inversion H0; inversion H | | now inversion H ].
        inversion H0; subst; [].
        match goal with x : ext_spec_type _ _  |- _ => clear -x end.
        now destruct e eqn:Ee; [ apply I | .. ];
          simpl in x;
          repeat match goal with
                   _ : context [ oi_eq_dec ?x ?y ] |- _ =>
                   destruct (oi_eq_dec x y); try discriminate; try tauto
                 end.
      }
      assert (Ex : exists name sig, ef = EF_external name sig) by (destruct ef; eauto; tauto).
      destruct Ex as (name & sg & ->); clear Hef.

      (* paragraph below: ef has to be an EF_external with one of those 5 names *)
      assert (which_primitive :
                Some (ext_link "acquire", LOCK_SIG) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "release", UNLOCK_SIG) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "makelock", ef_sig MKLOCK) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "freelock", ef_sig FREE_LOCK) = (ef_id_sig ext_link (EF_external name sg)) \/
                Some (ext_link "spawn", CREATE_SIG) = (ef_id_sig ext_link (EF_external name sg))).
      {
        pose proof (safety i cnti tt) as safe_i.
        rewrite Eci in safe_i.
        fixsafe safe_i.
        inversion safe_i; subst; [ now inversion H0; inversion H | | now inversion H ].
        inversion H0; subst; [].
        match goal with H : ext_spec_type _ _  |- _ => clear -H end.
        simpl in *.
        repeat match goal with
                 _ : context [ oi_eq_dec ?x ?y ] |- _ =>
                 destruct (oi_eq_dec x y); try injection e; auto
               end.
        tauto.
      }

      (* Before going any further, one needs to provide the first
        rmap of the oracle.  Unfortunately, for that, we need to know
        whether we're in an "acquire" external call or not. In
        addition, in the case of an "acquire" we need to know the
        arguments of the function (address+mpred) so that we can
        provide the right rmap from the lock set.
        |
        Two solutions: either we use a dummy oracle to know those things (but
        ... we need the oracle before that (FIX the spec OR [A]), or we write
        it as a P\/~P and then we derive a contradiction (not sure we can do
        that). *)

      destruct which_primitive as
          [ H_acquire | [ H_release | [ H_makelock | [ H_freelock | H_spawn ] ] ] ].

      { (* the case of acquire *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        unfold jsafeN, juicy_safety.safeN in safei.
        fixsafe safei.
        inversion safei
          as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
          [ now inversion bad; inversion H | subst | now inversion bad ].
        subst.
        simpl in at_ex. injection at_ex as <- <- .
        hnf in x.
        revert x Pre SafePost.

        Local Notation "{| 'JE_spec ... |}" := {| JE_spec := _; JE_pre_hered := _; JE_post_hered := _; JE_exit_hered := _ |}.

        (* dependent destruction *)
        funspec_destruct "acquire".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.

        (* relate lset to val *)
        destruct Precond as [PREA [[PREB _] PREC]].
        hnf in PREB.
        unfold canon.SEPx in PREC.
        simpl in PREC.
        rewrite seplog.sepcon_emp in PREC.
        pose proof PREC as islock.
        apply lock_inv_at in islock.

        assert (SUB : join_sub phi0 Phi). {
          apply join_sub_trans with  (ThreadPool.getThreadR cnti).
          - econstructor; eauto.
          - apply compatible_threadRes_sub; eauto.
            destruct compat; eauto.
        }
        destruct islock as [b [ofs [-> [R islock]]]].
        pose proof (resource_at_join_sub _ _ (b, Int.unsigned ofs) SUB) as SUB'.
        pose proof islock_pred_join_sub SUB' islock as isl.

        (* PLAN
           - DONE: integrate the oracle in the semax_conc definitions
           - DONE: sort out this dependent type problem
           - DONE: exploit jsafeN_ to figure out which possible cases
           - DONE: push the analysis through Krun/Kblocked/Kresume
           - DONE: figure a wait out of the ext_link problem (the LOCK
             should be a parameter of the whole thing)
           - DONE: change the lock_coherence invariants to talk about
             Mem.load instead of directly reading the values, since
             this will be abstracted
           - DONE: acquire-fail: still problems (see below)
           - DONE: acquire-success: the invariant guarantees that the
             rmap in the lockset satisfies the invariant.  We can give
             this rmap as a first step to the oracle.  We again have
             to recover the fact that all oracles after this step will
             be fine as well.
           - TODO: spawning: it introduces a new Kinit, change
             invariant accordingly
           - DONE release: this time, the jsafeN_ will explain how to
             split the current rmap.
         *)


        (* next step depends on status of lock: *)
        pose proof (lock_coh (b, Int.unsigned ofs)) as lock_coh'.
        destruct (AMap.find (elt:=option rmap) (b, Int.unsigned ofs) (ThreadPool.lset tp))
          as [[unlockedphi|]|] eqn:Efind;
          swap 1 3.
        (* inversion lock_coh' as [wetv dryv notlock H H1 H2 | R0 wetv isl' Elockset Ewet Edry | R0 phi wetv isl' SAT_R_Phi Elockset Ewet Edry]. *)

        - (* None: that cannot be: there is no lock at that address *)
          exfalso.
          destruct isl as [x [? [? EPhi]]].
          rewrite EPhi in lock_coh'.
          rewrite <-isLK_rewrite in lock_coh'.
          eapply ((* proj1 *) (lock_coh' _ _ _ _)).
          reflexivity.

        - (* Some None: lock is locked, so [acquire] fails. *)
          destruct lock_coh' as [LOAD ((* sh' & *) align & bound & R' & lk)].
          destruct isl as [sh [psh [z Ewetv]]].
          rewrite Ewetv in *.

          (* rewrite Eat in Ewetv. *)
          specialize (lk (b, Int.unsigned ofs)).
          spec lk. unfold LKSIZE in *; split; auto; omega.
          if_tac in lk. 2:tauto.

          unfold lock_inv in PREC.
          destruct PREC as (b0 & ofs0 & EQ & LKSPEC).
          injection EQ as <- <-.
          exists (m, ge, (sch, tp))(* ; split *).
          + apply state_step_c.
            apply JuicyMachine.sync_step with
            (Htid := cnti)
              (Hcmpt := mem_compatible_forget compat)
              (ev := Events.failacq (b, Int.intval (* replace with unsigned? *) ofs));
              [ reflexivity (* schedPeek *)
              | reflexivity (* schedSkip *)
              | ].
            (* factoring proofs out before the inversion/eapply *)
            pose proof LKSPEC as LKSPEC'.
            specialize (LKSPEC (b, Int.unsigned ofs)).
            simpl in LKSPEC.
            if_tac [r|nr] in LKSPEC; swap 1 2.
            { destruct nr.
              unfold LKSIZE; simpl.
              split. reflexivity. omega. }
            if_tac in LKSPEC; [ | congruence ].
            destruct LKSPEC as (p & E).
            pose proof (resource_at_join _ _ _ (b, Int.unsigned ofs) Join) as J.
            rewrite E in J.

            assert (Ename : name = "acquire"). {
              simpl in *.
              injection H_acquire as Ee.
              apply ext_link_inj in Ee; auto.
            }

            assert (Ez : z = LKSIZE). {
              simpl in lk.
              destruct lk as (psh' & rsh & EPhi).
              rewrite EPhi in Ewetv.
              injection Ewetv as _ <-.
              reflexivity.
            }

            assert (Esg : sg = LOCK_SIG) by (unfold ef_id_sig in *; congruence).

            assert (Eargs : args = Vptr b ofs :: nil). {
              subst sg.
              eapply shape_of_args; eauto.
            }

            assert (Ecall: EF_external name sg = LOCK) by congruence.

            assert (Eae : at_external SEM.Sem (ExtCall (EF_external name sg) args lid ve te k) =
                    Some (LOCK, Vptr b ofs :: nil)). {
              simpl.
              unfold SEM.Sem in *.
              rewrite SEM.CLN_msem; simpl.
              repeat f_equal; congruence.
            }

            unfold load_at in LOAD.
            eapply load_at_phi_restrict with (phi0 := phi0) (cnti := cnti) in LOAD.
            all: [ > | exists phi1; eassumption | eassumption | eassumption ].

            inversion J; subst.

            * eapply step_acqfail with (Hcompatible := mem_compatible_forget compat)
                                       (R0 := approx (level phi0) Rx).
              all: try solve [ constructor | eassumption | reflexivity ].
                (* [ > idtac ]. *)
              simpl.
              unfold Int.unsigned in *.
              rewr (getThreadR cnti @ (b, Int.intval ofs)).
              reflexivity.
              
            * eapply step_acqfail with (Hcompatible := mem_compatible_forget compat)
                                       (R0 := approx (level phi0) Rx).
              all: try solve [ constructor | eassumption | reflexivity ].
              simpl.
              unfold Int.unsigned in *.
              rewr (getThreadR cnti @ (b, Int.intval ofs)).
              reflexivity.

        - (* acquire succeeds *)
          destruct isl as [sh [psh [z Ewetv]]].
          destruct lock_coh' as [LOAD ((* sh' &  *)align & bound & R' & lk & sat)].
          rewrite Ewetv in *.

          unfold lock_inv in PREC.
          destruct PREC as (b0 & ofs0 & EQ & LKSPEC).
          injection EQ as <- <-.

          specialize (lk (b, Int.unsigned ofs)).
          spec lk. hnf. unfold LKSIZE in *; split; auto; omega.
          if_tac in lk. 2:tauto.
          destruct sat as [sat | sat]; [ | omega ].

          assert (Ename : name = "acquire"). {
            simpl in *.
            injection H_acquire as Ee.
            apply ext_link_inj in Ee; auto.
          }

          assert (Ez : z = LKSIZE). {
            simpl in lk.
            destruct lk as (psh' & rsh & EPhi).
            rewrite EPhi in Ewetv.
            injection Ewetv as _ <-.
            reflexivity.
          }

          assert (Esg : sg = LOCK_SIG) by (unfold ef_id_sig in *; congruence).

          assert (Eargs : args = Vptr b ofs :: nil). {
            subst sg.
            eapply shape_of_args; eauto.
          }

          assert (Ecall: EF_external name sg = LOCK) by congruence.

          assert (Eae : at_external SEM.Sem (ExtCall (EF_external name sg) args lid ve te k) =
                        Some (LOCK, Vptr b ofs :: nil)). {
            simpl.
            unfold SEM.Sem in *.
            rewrite SEM.CLN_msem; simpl.
            repeat f_equal; congruence.
          }

          assert (Hlt': permMapLt
                          (setPermBlock
                             (Some Writable) b (Int.intval ofs)
                             (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat) (getMaxPerm m)).
          {
            clear -Efind compat.
            clear -Efind compat.
            eapply permMapLt_local_locks; eauto.
          }

          (* changing value of lock in dry mem *)
          assert (Hm' : exists m', Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint Int.zero) = Some m'). {
            Transparent Mem.store.
            unfold Mem.store in *.
            destruct (Mem.valid_access_dec _ Mint32 b (Int.intval ofs) Writable) as [N|N].
            now eauto.
            exfalso.
            apply N.
            clear -Efind lock_coh align.
            eapply valid_access_restrPermMap; eauto.
          }
          destruct Hm' as (m', Hm').

          (* joinability condition provided by invariant : phi' will
          be the thread's new rmap *)
          destruct (compatible_threadRes_lockRes_join (mem_compatible_forget compat) cnti _ Efind)
            as (phi', Jphi').

          (* necessary to know that we have indeed a lock *)
          assert (ex: exists sh0 psh0, phi0 @ (b, Int.intval ofs) = YES sh0 psh0 (LK LKSIZE) (pack_res_inv (approx (level phi0) Rx))). {
            clear -LKSPEC.
            specialize (LKSPEC (b, Int.intval ofs)).
            simpl in LKSPEC.
            if_tac in LKSPEC. 2:range_tac.
            if_tac in LKSPEC. 2:tauto.
            destruct LKSPEC as (p, E).
            do 2 eexists.
            apply E.
          }
          destruct ex as (sh0 & psh0 & ex).
          pose proof (resource_at_join _ _ _ (b, Int.intval ofs) Join) as Join'.
          destruct (join_YES_l Join' ex) as (sh3 & sh3' & E3).

          eexists (m', ge, (sch, _)).
          + (* taking the step *)
            apply state_step_c.
            apply JuicyMachine.sync_step
            with (ev := (Events.acquire (b, Int.intval ofs) None))
                   (tid := i)
                   (Htid := cnti)
                   (Hcmpt := mem_compatible_forget compat)
            ;
              [ reflexivity | reflexivity | ].
            eapply step_acquire
            with (R0 := approx (level phi0) Rx)
            (* with (sh := shx) *)
            .
            all: try match goal with |- _ = age_tp_to _ _ => reflexivity end.
            all: try match goal with |- _ = updLockSet _ _ _ => reflexivity end.
            all: try match goal with |- _ = updThread _ _ _ => reflexivity end.
            * now auto.
            * eassumption.
            * simpl.
              unfold SEM.Sem in *.
              rewrite SEM.CLN_msem.
              simpl.
              repeat f_equal; [ | | ].
              -- simpl in H_acquire.
                 injection H_acquire as Ee.
                 apply ext_link_inj in Ee.
                 rewrite <-Ee.
                 reflexivity.
              -- auto.
              -- auto.
            * apply (mem_compatible_forget compat).
            * reflexivity.
            * unfold fold_right in *.
              rewrite E3.
              f_equal.
            * reflexivity.
            * eapply load_at_phi_restrict with (phi0 := phi0) (cnti := cnti) in LOAD.
              all: [ > assumption | exists phi1; eassumption | eassumption | eassumption ].
            * reflexivity.
            * reflexivity.
            * apply Hm'.
            * apply Efind.
            * apply Jphi'.
      }

      { (* the case of release *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        unfold jsafeN, juicy_safety.safeN in safei.
        inversion safei
          as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
          [ now inversion bad; inversion H | subst | now inversion bad ].
        subst.
        simpl in at_ex. injection at_ex as <- <- .
        hnf in x.
        revert x Pre SafePost.

        (* dependent destruction *)
        funspec_destruct "acquire".
        funspec_destruct "release".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.

        (* relate lset to val *)
        destruct Precond as ((Hreadable & PreA2) & (PreB1 & PreB2) & PreC).
        change Logic.True in PreA2. clear PreA2.
        change Logic.True in PreB2. clear PreB2.
        unfold canon.SEPx in PreC.
        unfold base.fold_right_sepcon in *.
        rewrite seplog.sepcon_emp in PreC.
        rewrite seplog.corable_andp_sepcon1 in PreC; swap 1 2.
        { apply seplog.corable_andp.
          apply corable_weak_precise.
          apply corable_weak_positive. }
        rewrite seplog.sepcon_comm in PreC.
        rewrite seplog.sepcon_emp in PreC.
        destruct PreC as ((Hprecise & Hpositive), PreC).
        destruct PreC as (phi_lockinv & phi_sat & jphi & Hlockinv & SAT).
        pose proof Hlockinv as islock.
        apply lock_inv_at in islock.

        assert (SUB : join_sub phi_lockinv Phi). {
          apply join_sub_trans with phi0. econstructor; eauto.
          apply join_sub_trans with (getThreadR cnti). econstructor; eauto.
          apply compatible_threadRes_sub; eauto. apply compat.
        }
        destruct islock as [b [ofs [-> [R islock]]]].
        pose proof (resource_at_join_sub _ _ (b, Int.unsigned ofs) SUB) as SUB'.
        pose proof islock_pred_join_sub SUB' islock as isl.

        (* next step depends on status of lock: *)
        pose proof (lock_coh (b, Int.unsigned ofs)) as lock_coh'.
        destruct (AMap.find (elt:=option rmap) (b, Int.unsigned ofs) (ThreadPool.lset tp))
          as [[unlockedphi|]|] eqn:Efind;
          swap 1 3.

        - (* None: that cannot be: there is no lock at that address *)
          exfalso.
          destruct isl as [x [? [? EPhi]]].
          rewrite EPhi in lock_coh'.
          rewrite <-isLK_rewrite in lock_coh'.
          (* rewrite <-isLKCT_rewrite in lock_coh'. *)
          eapply ((* proj1 *) (lock_coh' _ _ _ _)).
          reflexivity.

        - (* Some None: lock is locked, so [release] should succeed. *)
          destruct lock_coh' as [LOAD ((* sh' &  *)align & bound & R' & lk)].
          destruct isl as [sh [psh [z Ewetv]]].
          rewrite Ewetv in *.

          (* rewrite Eat in Ewetv. *)
          specialize (lk (b, Int.unsigned ofs)).
          spec lk.
          { hnf. unfold LKSIZE in *; split; auto; omega. }
          if_tac in lk. 2:tauto.
          destruct lk as (sh' & rsh & EPhi).

          assert (Ename : name = "release"). {
            simpl in *.
            injection H_release as Ee.
            apply ext_link_inj in Ee; auto.
          }

          assert (Ez : z = LKSIZE). {
            rewrite EPhi in Ewetv.
            injection Ewetv as _ <-.
            reflexivity.
          }

          assert (Esg : sg = LOCK_SIG) by (unfold ef_id_sig in *; congruence).

          assert (Eargs : args = Vptr b ofs :: nil). {
            subst sg.
            hnf in PreB1.
            eapply shape_of_args; eauto.
          }

          assert (Ecall: EF_external name sg = UNLOCK) by congruence.

          assert (Eae : at_external SEM.Sem (ExtCall (EF_external name sg) args lid ve te k) =
                        Some (UNLOCK, Vptr b ofs :: nil)). {
            simpl.
            unfold SEM.Sem in *.
            rewrite SEM.CLN_msem; simpl.
            auto.
          }
          subst z.

          assert (E1: exists sh sh', getThreadR cnti @ (b, Int.intval ofs) = YES sh sh' (LK LKSIZE) (pack_res_inv R)).
          {
            revert Join jphi SUB' islock; clear.
            unfold Int.unsigned in *.
            generalize (b, Int.intval ofs); intros l. clear b ofs.
            intros A B (r, C).
            apply resource_at_join with (loc := l) in A.
            apply resource_at_join with (loc := l) in B.
            unfold islock_pred in *.
            intros (sh1 & sh1' & z & E).
            rewr (phi_lockinv @ l) in C; inv C;
              rewr (phi_lockinv @ l) in B; inv B;
                rewr (phi0 @ l) in A; inv A;
                  eauto.
          }
          destruct E1 as (sh1 & sh1' & E1).

          assert (Hlt': permMapLt
                          (setPermBlock
                             (Some Writable) b (Int.intval ofs)
                             (juice2Perm_locks (getThreadR cnti) m) LKSIZE_nat) (getMaxPerm m)).
          {
            clear -Efind compat.
            clear -Efind compat.
            eapply permMapLt_local_locks; eauto.
          }

          (* changing value of lock in dry mem *)
          assert (Hm' : exists m', Mem.store Mint32 (restrPermMap Hlt') b (Int.intval ofs) (Vint Int.one) = Some m'). {
            Transparent Mem.store.
            unfold Mem.store in *.
            destruct (Mem.valid_access_dec _ Mint32 b (Int.intval ofs) Writable) as [N|N].
            now eauto.
            exfalso.
            apply N.
            clear -Efind lock_coh align.
            eapply valid_access_restrPermMap; eauto.
          }
          destruct Hm' as (m', Hm').

          (* remove [phi_sat] from [getThreadR cnti] to get the new [phi'] *)
          assert (Hphi' : exists phi',
                     join phi_lockinv phi1 phi' /\
                     join phi' phi_sat (getThreadR cnti)). {
            repeat match goal with H : join _ _ _ |- _ => revert H end; clear; intros.
            apply join_comm in jphi.
            destruct (sepalg.join_assoc jphi Join) as (phi' & j1 & j2).
            eauto.
          }
          destruct Hphi' as (phi' & Ephi' & Join_with_sat).

          assert (Sat : R (age_by 1 phi_sat)). {
            clear Post Hm' safei Eci Heq_name Heq_name0 LOAD Eae.
            apply predat4 in Hlockinv.
            apply predat5 in islock.
            pose proof predat_inj islock Hlockinv.
            subst R.
            split.
            - rewrite level_age_by.
              replace (level phi_sat) with (level Phi) by join_level_tac.
              replace (level phi_lockinv) with (level Phi) by join_level_tac.
              omega.
            - hered. 2: apply pred_hered.
              apply age_by_1. replace (level phi_sat) with (level Phi). omega. join_level_tac.
          }

          eexists (m', ge, (sch, _)).
          eapply state_step_c.
          eapply JuicyMachine.sync_step with (Htid := cnti); auto.
          eapply step_release
          with (c := (ExtCall (EF_external name sg) args lid ve te k))
                 (Hcompat := mem_compatible_forget compat);
              try apply Eci;
            try apply Eae;
            try apply Eci;
            try apply Hm';
            try apply E1;
            try eapply join_comm, Join_with_sat;
            try apply Wjm';
            try apply Sat;
            try apply Efind;
            try reflexivity.
          + apply (mem_compatible_forget compat).
          + destruct Hlockinv as (b00 & ofs00 & E & WOB); injection E as <- <-.
            eapply load_at_phi_restrict with (phi0 := phi_lockinv) (cnti := cnti) in LOAD.
            all: [ > assumption | | | eassumption ].
            * apply join_sub_trans with phi0. eexists; eauto.
              eexists. eapply join_comm. eauto.
            * eassumption.

        - (* Some Some: lock is unlocked, this should be impossible *)
          destruct lock_coh' as [LOAD (align & bound & R' & lk & sat)].
          destruct sat as [sat | ?]; [ | congruence ].
          destruct isl as [sh [psh [z Ewetv]]].
          rewrite Ewetv in *.
          exfalso.
          clear Post.

          (* sketch: *)
          (* - [unlockedphi] satisfies R *)
          (* - [phi_sat] satisfies R *)
          (* - [unlockedphi] and [phi_sat] join *)
          (* - but R is positive and precise so that's impossible *)

          pose proof predat6 lk as E1.
          pose proof predat1 Ewetv as E2.
          pose proof predat4 Hlockinv as E3.
          apply (predat_join_sub SUB) in E3.
          assert (level phi_lockinv = level Phi) by apply join_sub_level, SUB.
          assert (level unlockedphi = level Phi).
          { eapply join_sub_level, compatible_lockRes_sub; eauto; apply compat. }
          rewr (level phi_lockinv) in E3.
          assert (join_sub phi_sat Phi). {
            apply join_sub_trans with phi0. hnf; eauto.
            apply join_sub_trans with (getThreadR cnti). hnf; eauto.
            apply compatible_threadRes_sub. apply compat.
          }
          assert (level phi_sat = level Phi) by (apply join_sub_level; auto).

          pose proof (* weak_ *)positive_precise_joins_false
               (approx (level Phi) R) (age_by 1 unlockedphi) (age_by 1 phi_sat) (* phi0 *) as PP.
          apply PP.
          (* + (* level *) *)
          (*   rewrite !level_age_by. f_equal. join_level_tac. *)

          + (* positive *)
            apply positive_approx with (n := level Phi) in Hpositive.
            rewrite (compose_rewr (approx _) (approx _)) in Hpositive.
            replace (level phi0) with (level Phi) in Hpositive. 2:join_level_tac.
            exact_eq Hpositive; f_equal.
            eapply predat_inj; eauto.
            rewrite approx_oo_approx'. auto. omega.

          + (* precise *)
            unfold approx.
            apply precise_approx with (n := level Phi) in Hprecise.
            rewrite (compose_rewr (approx _) (approx _)) in Hprecise.
            replace (level phi0) with (level Phi) in Hprecise. 2:join_level_tac.
            exact_eq Hprecise; f_equal.
            eapply predat_inj; eauto.
            rewrite approx_oo_approx'. auto. omega.

          + (* sat 1 *)
            split.
            * rewrite level_age_by. rewr (level unlockedphi). omega.
            * revert sat.
              apply approx_eq_app_pred with (level Phi).
              -- rewrite level_age_by. rewr (level unlockedphi). omega.
              -- eapply predat_inj; eauto.

          + (* sat 2 *)
            split.
            -- rewrite level_age_by. rewr (level phi_sat). omega.
            -- cut (app_pred Rx (age_by 1 phi_sat)).
               ++ apply approx_eq_app_pred with (S n).
                  ** rewrite level_age_by. rewr (level phi_sat). omega.
                  ** pose proof (predat_inj E3 E2) as G.
                     exact_eq G; do 2 f_equal; auto.
               ++ revert SAT. apply age_by_ind.
                  destruct Rx.
                  auto.

          + (* joins *)
            apply age_by_joins.
            apply joins_sym.
            eapply @join_sub_joins_trans with (c := phi0); auto. apply Perm_rmap.
            * exists phi_lockinv. apply join_comm. auto.
            * eapply @join_sub_joins_trans with (c := getThreadR cnti); auto. apply Perm_rmap.
              -- exists phi1. auto.
              -- eapply compatible_threadRes_lockRes_join. apply (mem_compatible_forget compat).
                 apply Efind.
      }

      { (* the case of makelock *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        unfold jsafeN, juicy_safety.safeN in safei.
        inversion safei
          as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
          [ now inversion bad; inversion H | subst | now inversion bad ].
        subst.
        simpl in at_ex. injection at_ex as <- <- .
        hnf in x.
        revert x Pre SafePost.

        (* dependent destruction *)
        funspec_destruct "acquire".
        funspec_destruct "release".
        funspec_destruct "makelock".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.
        Set Printing Notations.

        assert (Ename : name = "makelock"). {
          simpl in *.
          injection H_makelock as Ee.
          apply ext_link_inj in Ee; auto.
        }

        assert (Esg : sg = UNLOCK_SIG) by (unfold ef_id_sig, ef_sig in *; congruence).

        destruct Precond as [[Hwritable _] [[B1 _] AT]].
        assert (Hreadable : readable_share shx) by (apply writable_readable; auto).

        (* [data_at_] from the precondition *)
        unfold canon.SEPx in *.
        simpl in AT.
        rewrite seplog.sepcon_emp in AT.

        (* value of [vx] *)
        simpl in B1.
        unfold lift, liftx in B1. simpl in B1.
        unfold lift, liftx in B1. simpl in B1.
        rewrite data_at__isptr in AT.
        destruct AT as (IsPtr, AT).
        destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].

        assert (Eargs : args = Vptr b ofs :: nil). {
          subst sg.
          eapply shape_of_args; eauto.
        }

        assert (Ecall: EF_external name sg = MKLOCK) by congruence.

        assert (Eae : at_external SEM.Sem (ExtCall (EF_external name sg) args lid ve te k) =
                      Some (MKLOCK, Vptr b ofs :: nil)). {
          simpl.
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem; simpl.
          repeat f_equal; congruence.
        }

        assert (Hm' : exists m', Mem.store Mint32 (m_dry (personal_mem (thread_mem_compatible (mem_compatible_forget compat) cnti))) b (Int.intval ofs) (Vint Int.zero) = Some m'). {
          clear -AT Join Hwritable.
          unfold tlock in AT. 
          destruct AT as (AT1, AT2). 
          destruct AT2 as [A B].
          clear A. (* it is 4 = 4 *)
          simpl in B. unfold mapsto_memory_block.at_offset in B.
          simpl in B. unfold nested_field_lemmas.nested_field_offset in B.
          simpl in B. unfold nested_field_lemmas.nested_field_type in B.
          simpl in B. unfold reptype_lemmas.default_val in B.
          simpl in B. unfold sublist.Znth in B.
          simpl in B. repeat rewrite Int.add_assoc in B.
          unfold data_at_rec_lemmas.data_at_rec in *.
          simpl in B.
          repeat rewrite add_repr in B.
          rewrite seplog.sepcon_emp in B. simpl in B.
          (* if array size > 4:
          destruct B as (phi00 & phi01 & jphi0 & B & _).
          *)
          unfold SeparationLogic.mapsto in *.
          simpl in B.
          destruct (readable_share_dec shx) as [n|n]. 2: now destruct n; apply writable_readable; auto.
          autorewrite with norm in B.
          rewrite !FF_orp in B.
          autorewrite with norm in B.
          destruct B as [v1' B]. 
          autorewrite with norm in B.
          destruct B as [v2' B]. 
          rewrite !TT_andp in B.
          apply mapsto_can_store with (v := v2') (sh := shx); try assumption.
          simpl (m_phi _).
          destruct B as [phi0a [phi0b [? [? ?]]]].
          destruct (join_assoc H Join) as [f [? ?]].
          exists phi0a, f; repeat split; auto.
          
        }
        destruct Hm' as (m', Hm').

        clear Post.

        unfold tlock in *.
        match type of AT with context[Tarray _ ?n] => assert (Hpos : (0 < n)%Z) by omega end.
        pose proof data_at_rmap_makelock CS as RL.
        specialize (RL shx b ofs Rx phi0 _ Hpos Hwritable AT).
        destruct RL as (phi0' & RL0 & lkat).

        match type of lkat with context[LK_at _ ?n] => assert (Hpos' : (0 < n)%Z) by omega end.
        pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos' RL0 Join as RL.
        destruct RL as (phi' & RLphi & j').
        assert (ji : join_sub (getThreadR cnti) Phi) by join_sub_tac.
        destruct ji as (psi & jpsi). cleanup.
        pose proof rmap_makelock_join _ _ _ _ _ _ _ Hpos' RLphi jpsi as RLPhi.
        destruct RLPhi as (Phi' & RLPhi & J').

        eexists (m', ge, (sch, _)).
        constructor.

        eapply JuicyMachine.sync_step
        with (Htid := cnti); auto.

        eapply step_mklock
        with (c := (ExtCall (EF_external name sg) args lid ve te k))
               (Hcompatible := mem_compatible_forget compat)
               (R := Rx)
               (phi'0 := phi')
        ; try eassumption; auto.
        constructor.
      }

      { (* the case of freelock *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        unfold jsafeN, juicy_safety.safeN in safei.
        inversion safei
          as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
          [ now inversion bad; inversion H | subst | now inversion bad ].
        subst.
        simpl in at_ex. injection at_ex as <- <- .
        hnf in x.
        revert x Pre SafePost.

        (* dependent destruction *)
        funspec_destruct "acquire".
        funspec_destruct "release".
        funspec_destruct "makelock".
        funspec_destruct "freelock".

        intros (phix, (ts, ((vx, shx), Rx))) (Hargsty, Pre).
        simpl (projT2 _) in *; simpl (fst _) in *; simpl (snd _) in *; clear ts.
        simpl in Pre.
        destruct Pre as (phi0 & phi1 & Join & Precond & HnecR).
        simpl (and _).
        intros Post.
        Set Printing Notations.

        assert (Ename : name = "freelock"). {
          simpl in *.
          injection H_freelock as Ee.
          apply ext_link_inj in Ee; auto.
        }

        assert (Esg : sg = UNLOCK_SIG) by (unfold ef_id_sig, ef_sig in *; congruence).

        destruct Precond as ((Hwritable & PreA2) & (B1 & PreB2) & PreC).
        change Logic.True in PreA2. clear PreA2.
        change Logic.True in PreB2. clear PreB2.
        unfold canon.SEPx in PreC.
        unfold base.fold_right_sepcon in *.
        rewrite seplog.sepcon_emp in PreC.
        rewrite seplog.corable_andp_sepcon1 in PreC; swap 1 2.
        { apply seplog.corable_andp.
          apply corable_weak_precise.
          apply corable_weak_positive. }
        rewrite seplog.sepcon_comm in PreC.
        rewrite seplog.sepcon_emp in PreC.
        destruct PreC as ((Hprecise & Hpositive), AT).
        (* pose proof AT as islock. *)
        (* apply lock_inv_at in islock. *)
        assert (Hreadable : readable_share shx) by (apply writable_readable; auto).

        (* [data_at_] from the precondition *)
        unfold canon.SEPx in *.
        simpl in AT.

        (* value of [vx] *)
        simpl in B1.
        unfold lift, liftx in B1. simpl in B1.
        unfold lift, liftx in B1. simpl in B1.
        rewrite lockinv_isptr in AT.

        destruct AT as (phi0lockinv & phi0sat & jphi0 & (IsPtr & Hlockinv) & Hsat).
        destruct vx as [ | | | | | b ofs ]; try inversion IsPtr; [ clear IsPtr ].

        assert (Eargs : args = Vptr b ofs :: nil). {
          subst sg.
          eapply shape_of_args; eauto.
        }

        assert (Ecall: EF_external name sg = FREE_LOCK) by congruence.

        assert (Eae : at_external SEM.Sem (ExtCall (EF_external name sg) args lid ve te k) =
                      Some (FREE_LOCK, Vptr b ofs :: nil)). {
          simpl.
          unfold SEM.Sem in *.
          rewrite SEM.CLN_msem; simpl.
          repeat f_equal; congruence.
        }

        clear Post.

        assert (lock_not_none : lockRes tp (b, Int.intval ofs) <> None). {
          spec lock_coh (b, Int.intval ofs). cleanup.
          destruct (AMap.find _ _) as [|] eqn:Ephi_sat. congruence.
          unfold lock_inv in *.
          destruct Hlockinv as (b_ & ofs_ & E_ & HH).
          spec HH (b, Int.intval ofs).
          simpl in HH.
          change Int.intval with Int.unsigned in *.
          injection E_ as <- <- .
          if_tac [r|nr] in HH. 2:range_tac.
          if_tac [e|ne] in HH. 2:tauto.
          destruct HH as (p & HH).
          assert (j : join_sub phi0lockinv Phi). {
            apply join_sub_trans with phi0. eexists; eauto.
            apply join_sub_trans with (@getThreadR i tp cnti). eexists; eauto.
            join_sub_tac.
          }
          destruct j as (psi' & j).
          apply resource_at_join with (loc := (b, Int.unsigned ofs)) in j.
          rewrite HH in j.
          destruct lock_coh.
          inv j; hnf; eauto.
        }

        pose proof Hlockinv as COPY.
        apply (lock_inv_rmap_freelock CS) with (m := m) in COPY; auto; try apply lock_coh; swap 1 2; swap 2 3.
        {
          spec lock_coh (b, Int.intval ofs). cleanup.
          remember (AMap.find (elt:=option rmap) _ _) as o in lock_coh.
          rewrite <-Heqo in lock_not_none.
          destruct o as [[phi_sat|]|]; [ | | ]; try solve [apply lock_coh].
          tauto.
        }
        {
          spec lock_coh (b, Int.intval ofs). cleanup.
          remember (AMap.find (elt:=option rmap) _ _) as o in lock_coh.
          rewrite <-Heqo in lock_not_none.
          destruct o as [[phi_sat|]|]; [ | | ]; try solve [apply lock_coh].
          tauto.
        }

        destruct COPY as (phi0lockinv' & Hrmap00 & Hlkat).

        assert (Hpos'' : (0 < LKSIZE)%Z) by (clear; unfold LKSIZE; omega). 
        pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' Hrmap00 jphi0 as Hrmap0.
        destruct Hrmap0 as (phi0' & Hrmap0 & jphi0').
        pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' Hrmap0 Join as Hrmap.
        pose proof Hrmap as Hrmap_.
        destruct Hrmap_ as (phi' & RLphi & j').
        assert (ji : join_sub (@getThreadR _ _ cnti) Phi) by join_sub_tac.
        destruct ji as (psi & jpsi). cleanup.
        pose proof rmap_freelock_join _ _ _ _ _ _ _ _ Hpos'' RLphi jpsi as Hrmap'.
        destruct Hrmap' as (Phi' & Hrmap' & J').

        assert (locked : lockRes tp (b, Int.intval ofs) = Some None). {
          spec lock_coh (b, Int.intval ofs). cleanup.
          destruct (AMap.find _ _) as [[phi_sat|]|] eqn:Ephi_sat; [ exfalso | reflexivity | exfalso ].
          - (* positive and precise *)
            destruct lock_coh as (_&_&_&R&lk&[sat|?]). 2:omega.

            assert (J0 : join_sub phi0 Phi). {
              apply join_sub_trans with (@getThreadR i tp cnti). eexists; eauto.
              join_sub_tac.
            }
            assert (Ja0 : join_sub phi0sat Phi).  {
              apply join_sub_trans with phi0; eauto. eexists; eauto.
            }
            assert (Ja : join_sub phi_sat Phi). {
              eapply compatible_lockRes_sub; eauto.
              apply compat.
            }
            assert (J01 : join_sub phi0lockinv Phi). {
              apply join_sub_trans with phi0. eexists; eauto.
              apply join_sub_trans with (@getThreadR i tp cnti). eexists; eauto.
              join_sub_tac.
            }
            assert (R01 : level phi0lockinv = level Phi) by join_level_tac.
            assert (Ra : level phi_sat = level Phi) by join_level_tac.
            assert (Ra0 : level phi0sat = level Phi) by join_level_tac.
            pose proof predat6 lk as E1.
            pose proof predat4 Hlockinv as E3.
            apply (predat_join_sub J01) in E3.

            pose proof positive_precise_joins_false
                 (approx (level Phi) Rx) (age_by 1 phi_sat) (age_by 1 phi0sat) as PP.
            apply PP.
            + (* positive *)
              apply positive_approx with (n := level Phi) in Hpositive.
              rewrite (compose_rewr (approx _) (approx _)) in Hpositive.
              rewrite approx_oo_approx' in Hpositive. auto.
              replace (level phi0) with (level Phi). 2:join_level_tac.
              omega.

            + (* precise *)
              apply precise_approx with (n := level Phi) in Hprecise.
              rewrite (compose_rewr (approx _) (approx _)) in Hprecise.
              rewrite approx_oo_approx' in Hprecise. auto.
              replace (level phi0) with (level Phi). 2:join_level_tac.
              omega.

            + (* sat 1 *)
              split.
              * rewrite level_age_by. rewrite Ra. omega.
              * revert sat.
                apply approx_eq_app_pred with (level Phi).
                -- rewrite level_age_by. rewr (level phi_sat). omega.
                -- eapply predat_inj; eauto.
                   apply predat6 in lk; eauto.
                   exact_eq E3. f_equal. f_equal. auto.

            + (* sat 2 *)
              split.
              -- rewrite level_age_by. cut (level phi0sat = level Phi). omega. join_level_tac.
              -- revert Hsat. apply age_by_ind.
                 destruct Rx.
                 auto.

            + (* joins *)
              apply age_by_joins.
              apply joins_sym.
              eapply @join_sub_joins_trans with (c := phi0); auto. apply Perm_rmap.
              * exists phi0lockinv. apply join_comm. auto.
              * eapply @join_sub_joins_trans with (c := @getThreadR i tp cnti); auto. apply Perm_rmap.
                -- exists phi1. auto.
                -- eapply compatible_threadRes_lockRes_join. apply (mem_compatible_forget compat).
                   apply Ephi_sat.

          - (* not a lock: impossible *)
            simpl in Hlockinv.
            unfold lock_inv in *.
            destruct Hlockinv as (b_ & ofs_ & E_ & HH).
            spec HH (b, Int.intval ofs).
            simpl in HH.
            change Int.intval with Int.unsigned in *.
            injection E_ as <- <- .
            if_tac [r|nr] in HH. 2:range_tac.
            if_tac [e|ne] in HH. 2:tauto.
            destruct HH as (p & HH).
            assert (j : join_sub phi0lockinv Phi). {
              apply join_sub_trans with phi0. eexists; eauto.
              apply join_sub_trans with (@getThreadR i tp cnti). eexists; eauto.
              join_sub_tac.
            }
            destruct j as (psi' & j).
            apply resource_at_join with (loc := (b, Int.unsigned ofs)) in j.
            rewrite HH in j.
            apply lock_coh.
            inv j; hnf; eauto.
        }

        eexists (m, ge, (sch, _)).
        constructor.

        eapply JuicyMachine.sync_step
        with (Htid := cnti); auto.

        eapply step_freelock
        with (c := (ExtCall (EF_external name sg) args lid ve te k))
               (Hcompat := mem_compatible_forget compat)
               (R := Rx)
               (phi'0 := phi')
        .

        all: try match goal with |- invariant _ => now constructor end.
        all: try match goal with |- _ = age_tp_to _ _ => reflexivity end.
        all: try match goal with |- _ = updThread _ _ _ => reflexivity end.
        all: try match goal with |- personal_mem _ = _ => reflexivity end.
        - assumption.
        - eassumption.
        - exists Phi; apply compat.
        - reflexivity.
        - assumption.
        - assumption.
      }

      { (* the case of spawn *)

        (* using the safety to prepare the precondition *)
        pose proof (safety i cnti tt) as safei.
        rewrite Eci in safei.
        fixsafe safei.
        unfold jsafeN, juicy_safety.safeN in safei.
        inversion safei
          as [ | ?????? bad | n0 z c m0 e args0 x at_ex Pre SafePost | ????? bad ];
          [ now inversion bad; inversion H | subst | now inversion bad ].
        subst.
        simpl in at_ex. injection at_ex as <- <- .
        hnf in x.
        revert x Pre SafePost.

        (* dependent spawn *)
        funspec_destruct "acquire".
        funspec_destruct "release".
        funspec_destruct "makelock".
        funspec_destruct "freelock".
        funspec_destruct "spawn".

        (* disregarding the case of makelock by hypothesis *)
        exfalso; apply not_spawn.
        repeat eexists; eauto.
        simpl.
        simpl in H_spawn.
        f_equal.
        f_equal.
        injection H_spawn. intros <- E.
        apply ext_link_inj in E.
        subst name.
        reflexivity.
      }
    }
    (* end of Kblocked *)

    (* thread[i] is in Kresume *)
    {
      (* goes to Krun ci' with after_ex ci = ci'  *)
      destruct ci as [ve te k | ef args lid ve te k] eqn:Heqc.

      - (* contradiction: has to be an extcall *)
        specialize (wellformed i cnti).
        rewrite Eci in wellformed.
        simpl in wellformed.
        tauto.

      - (* extcall *)
        pose (ci':=
                match lid with
                | Some id => State ve (Maps.PTree.set id Vundef te) k
                | None => State ve te k
                end).
        exists (m, ge, (i :: sch, ThreadPool.updThreadC cnti (Krun ci')))(* ; split *).
        + (* taking the step Kresume->Krun *)
          constructor.
          apply JuicyMachine.resume_step with (tid := i) (Htid := cnti).
          * reflexivity.
          * eapply mem_compatible_forget. eauto.
          * unfold SEM.Sem in *.
            eapply JuicyMachine.ResumeThread with (c := ci) (c' := ci');
              try rewrite SEM.CLN_msem in *;
              simpl.
            -- subst.
               unfold SEM.Sem in *.
               rewrite SEM.CLN_msem in *; simpl.
               reflexivity.
            -- subst.
               unfold SEM.Sem in *.
               rewrite SEM.CLN_msem in *; simpl.
               destruct lid.
               ++ spec wellformed i cnti. rewrite Eci in wellformed. destruct wellformed.
                  unfold ci'. reflexivity.
               ++ reflexivity.
            -- rewrite Eci.
               subst ci.
               f_equal.
               specialize (wellformed i cnti).
               rewrite Eci in wellformed.
               simpl in wellformed.
               tauto.
            -- constructor.
            -- reflexivity.
    }
    (* end of Kresume *)

    (* thread[i] is in Kinit *)
    {
      spec safety i cnti tt. rewrite Eci in safety.
      destruct safety as (q_new & Einit & safety).
      eexists(* ; split *).
      - constructor.
        apply JuicyMachine.start_step with (tid := i) (Htid := cnti).
        + reflexivity.
        + eapply mem_compatible_forget. eauto.
        + eapply JuicyMachine.StartThread with (c_new := q_new).
          * apply Eci.
          * replace (initial_core SEM.Sem _) with cl_initial_core. auto.
            unfold the_sem, SEM.Sem.
            rewrite SEM.CLN_msem.
            reflexivity.
          * constructor.
          * reflexivity.
    }
    (* end of Kinit *)
    Unshelve. eexists; eauto.
Qed. (* Theorem progress *)

End Progress.
