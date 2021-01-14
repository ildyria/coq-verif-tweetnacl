Require Import compcert.lib.Axioms.

Require Import VST.concurrency.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.concurrency.pos.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.addressFiniteMap. (*The finite maps*)
Require Import VST.concurrency.pos.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.semantics.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import VST.concurrency.threads_lemmas.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.permissions.
Require Import VST.concurrency.threadPool.

Module LocksAndResources.
  Definition res : Type := unit.
  Definition lock_info : Type := unit.
End LocksAndResources.

Module ThreadPool (SEM:Semantics)  <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES := LocksAndResources.
    Include (OrdinalPool SEM LocksAndResources).
End ThreadPool.


Module mySchedule := ListScheduler NatTID.

Module ErasedMachineShell (SEM:Semantics)  <: ConcurrentMachineSig
    with Module ThreadPool.TID:=mySchedule.TID
    with Module ThreadPool.SEM:= SEM
    with Module ThreadPool.RES:= LocksAndResources
    with Module Events.TID := mySchedule.TID.

   Module Events := Events.
   Module ThreadPool := ThreadPool SEM.
   Import ThreadPool.
   Import ThreadPool.SEM ThreadPool.RES.
   Import event_semantics Events.

   Notation tid := NatTID.tid.

   (** Memories*)
   Definition richMem: Type:= mem.
   Definition dryMem: richMem -> mem:= id.
   Definition diluteMem: mem -> mem := erasePerm.

   Notation thread_pool := (ThreadPool.t).
   Notation perm_map := ThreadPool.RES.res.

   (** The state respects the memory*)
   Definition mem_compatible (tp : thread_pool) (m : mem) : Prop := True.

   Definition invariant (tp : thread_pool) := True.

   (** Steps*)
   Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
             (Hcompatible: mem_compatible tp m) :
     thread_pool -> mem -> seq mem_event -> Prop :=
   | step_dry :
       forall (tp':thread_pool) c m' (c' : code) ev
         (Hcode: getThreadC cnt = Krun c)
         (Hcorestep: ev_step Sem genv c m ev c' m')
         (Htp': tp' = updThreadC cnt (Krun c')),
     dry_step genv cnt Hcompatible tp' m' ev.

   Inductive ext_step {isCoarse:bool} (genv:G) {tid0 tp m} (*Can we remove genv from here?*)
             (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
     thread_pool -> mem -> sync_event -> Prop :=
   | step_acquire :
       forall (tp' : thread_pool) c m' b ofs
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (LOCK, Vptr b ofs::nil))
         (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one))
         (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
         (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat tp' m' (acquire (b, Int.intval ofs) None)

   | step_release :
       forall (tp':thread_pool) c m' b ofs
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (UNLOCK, Vptr b ofs::nil))
         (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m')
         (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat tp' m' (release (b, Int.intval ofs) None)

   | step_create :
       forall (tp_upd tp':thread_pool) c b ofs arg
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (CREATE, Vptr b ofs::arg::nil))
         (Htp_upd: tp_upd = updThreadC cnt0 (Kresume c Vundef))
         (Htp': tp' = addThread tp_upd (Vptr b ofs) arg tt),
         ext_step genv cnt0 Hcompat tp' m (spawn (b, Int.intval ofs) None None)

   | step_mklock :
       forall  (tp': thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external Sem c =
                         Some (MKLOCK, Vptr b ofs::nil))
          (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat tp' m' (mklock (b, Int.intval ofs))

   | step_freelock :
       forall (tp' tp'': thread_pool) c b ofs
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (FREE_LOCK, Vptr b ofs::nil))
         (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat  tp' m (freelock (b,Int.intval ofs))

   | step_acqfail :
       forall  c b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external Sem c =
                         Some (LOCK, Vptr b ofs::nil))
          (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero)),
         ext_step genv cnt0 Hcompat tp m (failacq (b, Int.intval ofs)).

   Definition threadStep (genv : G): forall {tid0 ms m},
       containsThread ms tid0 -> mem_compatible ms m ->
       thread_pool -> mem -> seq mem_event -> Prop:=
     @dry_step genv.

   Lemma threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
   Proof.
     intros. split.
     - intros [cntj [ q running]].
       inversion H; subst.
        assert (cntj':=cntj).
        eapply (cntUpdateC (Krun c')) in cntj'.
        exists cntj'.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c'.
          rewrite gssThreadCC; reflexivity.
        + exists q.
          erewrite <- gsoThreadCC; eauto.
      - intros [cntj' [ q' running]].
        inversion H; subst.
        assert (cntj:=cntj').
        eapply cntUpdateC' with (c0:=Krun c') in cntj; eauto.
        exists cntj.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c.
          rewrite <- Hcode.
          f_equal.
          apply cnt_irr.
        + exists q'.
          erewrite <- gsoThreadCC in running; eauto.
   Qed.

   Definition syncStep (isCoarse:bool) (genv :G) :
     forall {tid0 ms m},
       containsThread ms tid0 -> mem_compatible ms m ->
       thread_pool -> mem -> sync_event -> Prop:=
     @ext_step isCoarse genv.

  Lemma syncstep_equal_run:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
  Proof.
    intros b g i tp m cnt cmpt tp' m' tr H j; split.
    - intros [cntj [ q running]].
      destruct (NatTID.eq_tid_dec i j).
      + subst j. generalize running; clear running.
        inversion H; subst;
          match goal with
          | [ H: getThreadC ?cnt = Kblocked ?c |- _ ] =>
            replace cnt with cntj in H by apply cnt_irr;
              intros HH; rewrite HH in H; inversion H
          end.
      + (*this should be easy to automate or shorten*)
        inversion H; subst.
        * exists (cntUpdateC (Kresume c Vundef) cnt cntj), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntUpdateC (Kresume c Vundef) cnt cntj), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntAdd _ _ _
                    (cntUpdateC (Kresume c Vundef) cnt cntj)), q.
          erewrite gsoAddCode; eauto. (*i? *)
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntUpdateC (Kresume c Vundef) cnt cntj), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists (cntRemoveL (b0, Int.intval ofs)
                        (cntUpdateC (Kresume c Vundef) cnt cntj)), q.
          erewrite <- gsoThreadCC; eassumption.
        * exists cntj, q; assumption.
    - intros [cntj [ q running]].
      destruct (NatTID.eq_tid_dec i j).
      + subst j. generalize running; clear running.
        inversion H; subst;
          try rewrite gRemLockSetCode;
          try rewrite gssThreadCC;
          try solve[intros HH; inversion HH].
        { (*addthread*)
          assert (cntj':=cntj).
          eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
          * erewrite gsoAddCode; eauto.
            subst; rewrite gssThreadCC; intros AA; inversion AA.
          * erewrite gssAddCode . intros AA; inversion AA.
            assumption. }
          { (*AQCUIRE*)
            replace cntj with cnt by apply cnt_irr.
            rewrite Hcode; intros HH; inversion HH. }
      + generalize running; clear running.
        inversion H; subst;
          try rewrite gRemLockSetCode;
          try (erewrite <- gsoThreadCC; [|eauto]);
        try (intros HH;
        match goal with
        | [ H: getThreadC ?cnt = Krun ?c |- _ ] =>
          exists cntj, c; exact H
        end).
      (*Add thread case*)
        assert (cntj':=cntj).
        eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
        * erewrite gsoAddCode; eauto.
          destruct (NatTID.eq_tid_dec i j);
            [subst; rewrite gssThreadCC; intros AA; inversion AA|].
          erewrite <- gsoThreadCC; eauto.
        * erewrite gssAddCode . intros AA; inversion AA.
          assumption.
          Grab Existential Variables.
          all: eauto.
  Qed.

  Lemma syncstep_not_running:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q.
  Proof.
    intros.
    inversion H;
      match goal with
      | [ H: getThreadC ?cnt = _ |- _ ] =>
        erewrite (cnt_irr _ cnt);
          rewrite H; intros AA; inversion AA
      end.
  Qed.

   Inductive threadHalted': forall {tid0 ms},
       containsThread ms tid0 -> Prop:=
   | thread_halted':
       forall tp c tid0
         (cnt: containsThread tp tid0)
         (Hcode: getThreadC cnt = Krun c)
         (Hcant: halted Sem c),
         threadHalted' cnt.

   Definition threadHalted: forall {tid0 ms},
       containsThread ms tid0 -> Prop:= @threadHalted'.


  Lemma threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') .
  Proof.
    intros; split; intros HH; inversion HH; subst;
    econstructor; eauto.
    erewrite <- (gsoThreadCC H); exact Hcode.
    erewrite (gsoThreadCC H); exact Hcode.
  Qed.

  Lemma syncstep_equal_halted:
    forall b g i tp m cnti cmpt tp' m' tr,
      @syncStep b g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').
  Proof.
    intros; split; intros HH; inversion HH; subst;
    econstructor; subst; eauto.
    - destruct (NatTID.eq_tid_dec i j).
      + subst j.
        inversion H;
          match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
            replace cnt with cnt' in H by apply cnt_irr;
              rewrite H' in H; inversion H
          end.
      + inversion H; subst;
          try rewrite gRemLockSetCode;
          try erewrite gsoAddCode; eauto;
          try erewrite <- gsoThreadCC; try eassumption.
        { (*AQCUIRE*)
            replace cnt' with cnt0 by apply cnt_irr;
          exact Hcode. }
    - destruct (NatTID.eq_tid_dec i j).
      + subst j.
        inversion H; subst;
        match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
              try rewrite gRemLockSetCode in H;
              try erewrite gsoAddCode in H; eauto;
              try erewrite gssThreadCC in H;
              try solve[inversion H]
        end.
        { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
          exact Hcode. }
      +
        inversion H; subst;
        match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
              try rewrite gRemLockSetCode in H;
              try erewrite gsoAddCode in H; eauto;
              try erewrite <- gsoThreadCC in H; eauto;
              try solve[inversion H]; eauto
        end.
        { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
          exact Hcode. }

        Grab Existential Variables.
        all:eauto.
  Qed.

  Lemma threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .
  Proof.
    intros; inversion H; inversion H0; subst.
    destruct (NatTID.eq_tid_dec i j).
    - subst j. simpl in Hcorestep.
      eapply ev_step_ax1 in Hcorestep.
      eapply corestep_not_halted in Hcorestep.
      replace cnt1 with cnt in Hcode0 by apply cnt_irr.
      rewrite Hcode0 in Hcode; inversion Hcode;
      subst c0.
      rewrite Hcorestep in Hcant; inversion Hcant.
    - econstructor; eauto.
      erewrite <- gsoThreadCC; eauto.
  Qed.

   Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

   Definition initial_machine c :=
     ThreadPool.mk
       one_pos
       (fun _ =>  Krun c)
       (fun _ => tt)
       empty_lset.

   Definition init_mach (_ : option unit) (genv:G)
              (v:val)(args:list val):option thread_pool :=
     match initial_core Sem 0 genv v args with
     | Some c =>
       Some (initial_machine c)
     | None => None
     end.

End ErasedMachineShell.

