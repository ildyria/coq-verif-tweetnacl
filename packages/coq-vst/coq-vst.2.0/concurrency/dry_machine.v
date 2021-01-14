Require Import compcert.lib.Axioms.

Require Import VST.concurrency.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.pos.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.TheSchedule.
Require Import VST.concurrency.concurrent_machine.
Require Import VST.concurrency.addressFiniteMap. (*The finite maps*)
Require Import VST.concurrency.pos.
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permjoin_def.
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
Require Import VST.concurrency.semantics.
Require Import VST.concurrency.TheSchedule. Import TheSchedule.

Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.permissions.
Require Import VST.concurrency.bounded_maps.
Require Import VST.concurrency.threadPool.

Module LocksAndResources.
  (** Dry resources are one permission map for non-lock locations and another for lock
  locations*)
  Definition res := (access_map * access_map)%type.
  Definition lock_info := (access_map * access_map)%type.
End LocksAndResources.


Module ThreadPool (SEM:Semantics)  <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES := LocksAndResources.

    Include (OrdinalPool SEM LocksAndResources).

End ThreadPool.

Module Concur.

  Module mySchedule := THESCH.

  (** The type of dry machines. This is basically the same as
  [ConcurrentMachineSig] but resources are instantiated with dry
  resources*)
  Module Type DryMachineSig  (SEM: Semantics) <: ConcurrentMachineSig
      with Module ThreadPool.RES:= LocksAndResources
      with Module ThreadPool.TID:=mySchedule.TID.

     Declare Module Events : EventSig.
     Module ThreadPool := ThreadPool SEM.
     Import ThreadPool SEM.
     Import event_semantics Events.

     (** Memories*)
     Definition richMem: Type:= mem.
     Definition dryMem: richMem -> mem:= id.
     Definition diluteMem: mem -> mem := setMaxPerm.

     Notation thread_pool := (ThreadPool.t).

     (** The state respects the memory*)
     Record mem_compatible' tp m : Prop :=
       { compat_th :> forall {tid} (cnt: containsThread tp tid),
             permMapLt (getThreadR cnt).1 (getMaxPerm m) /\
             permMapLt (getThreadR cnt).2 (getMaxPerm m);
         compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                                permMapLt pmaps.1 (getMaxPerm m) /\
                                permMapLt pmaps.2 (getMaxPerm m);
         lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                   Mem.valid_block m l.1}.

     Definition mem_compatible tp m : Prop := mem_compatible' tp m.

     Record invariant' tp :=
       { no_race_thr :
           forall i j (cnti: containsThread tp i) (cntj: containsThread tp j)
             (Hneq: i <> j),
             permMapsDisjoint2 (getThreadR cnti)
                              (getThreadR cntj); (*thread's resources are disjoint *)
         no_race_lr:
           forall laddr1 laddr2 rmap1 rmap2
             (Hneq: laddr1 <> laddr2)
             (Hres1: lockRes tp laddr1 = Some rmap1)
             (Hres2: lockRes tp laddr2 = Some rmap2),
             permMapsDisjoint2 rmap1 rmap2; (*lock's resources are disjoint *)
         no_race:
           forall i laddr (cnti: containsThread tp i) rmap
             (Hres: lockRes tp laddr = Some rmap),
             permMapsDisjoint2 (getThreadR cnti) rmap; (*resources are disjoint
             between threads and locks*)
         (* an address is in the lockres if there is at least one >= Readable
         lock permission - I am writing the weak version where this is required
         only for permissions of threads*)
         (* lock_res_perm: *)
         (*   forall b ofs, *)
         (*     (exists i (cnti: containsThread tp i), *)
         (*         Mem.perm_order' ((getThreadR cnti).2 !! b ofs) Readable) ->  *)
         (*     lockRes tp (b, ofs); *)

         (* if an address is a lock then there can be no data
             permission above non-empty for this address*)
         thread_data_lock_coh:
           forall i (cnti: containsThread tp i),
             (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 (getThreadR cnti).2) /\
             (forall laddr rmap,
                 lockRes tp laddr = Some rmap ->
                 permMapCoherence rmap.1 (getThreadR cnti).2);
         locks_data_lock_coh:
           forall laddr rmap
             (Hres: lockRes tp laddr = Some rmap),
             (forall j (cntj: containsThread tp j),
                 permMapCoherence (getThreadR cntj).1 rmap.2) /\
             (forall laddr' rmap',
                 lockRes tp laddr' = Some rmap' ->
                 permMapCoherence rmap'.1 rmap.2);
         lockRes_valid: lr_valid (lockRes tp) (*well-formed locks*)
       }.

     Definition invariant := invariant'.
     Parameter threadStep :
       G ->
       forall tid0 (ms : t) (m : mem),
         containsThread ms tid0 ->
         mem_compatible ms m -> t -> mem -> seq mem_event -> Prop.

     Axiom threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
     Parameter syncStep :
       bool -> (* if it's a Coarse machine. Temp solution to propagating changes. *)
       G ->
       forall tid0 (ms : t) (m : mem),
         containsThread ms tid0 ->
         mem_compatible ms m -> t -> mem -> sync_event -> Prop.

  Axiom syncstep_equal_run:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').

  Axiom syncstep_not_running:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q.


     Parameter threadHalted :
       forall tid0 (ms : t), containsThread ms tid0 -> Prop.
     Parameter init_mach : option RES.res -> G -> val -> seq val -> option t.



  Axiom threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') .

  Axiom syncstep_equal_halted:
    forall b g i tp m cnti cmpt tp' m' tr,
      @syncStep b g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').

  Axiom threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .

  End DryMachineSig.

  Module DryMachineShell (SEM:Semantics)  <: DryMachineSig SEM.

     Module Events := Events.
     Module ThreadPool := ThreadPool SEM.
     Import ThreadPool.
     Import ThreadPool.SEM ThreadPool.RES.
     Import event_semantics Events.

     Notation tid := NatTID.tid.

     (** Memories*)
     Definition richMem: Type:= mem.
     Definition dryMem: richMem -> mem:= id.
     Definition diluteMem: mem -> mem := setMaxPerm.

     Notation thread_pool := (ThreadPool.t).

     (** The state respects the memory*)

     Record mem_compatible' tp m : Prop :=
       { compat_th :> forall {tid} (cnt: containsThread tp tid),
             permMapLt (getThreadR cnt).1 (getMaxPerm m) /\
             permMapLt (getThreadR cnt).2 (getMaxPerm m);
         compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                                permMapLt pmaps.1 (getMaxPerm m) /\
                                permMapLt pmaps.2 (getMaxPerm m);
         lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                   Mem.valid_block m l.1}.

     Definition mem_compatible tp m : Prop := mem_compatible' tp m.


     (* should there be something that says that if something is a lock then
     someone has at least readable permission on it?*)
     Record invariant' tp :=
       { no_race_thr :
           forall i j (cnti: containsThread tp i) (cntj: containsThread tp j)
             (Hneq: i <> j),
             permMapsDisjoint2 (getThreadR cnti)
                              (getThreadR cntj); (*thread's resources are disjoint *)
         no_race_lr:
           forall laddr1 laddr2 rmap1 rmap2
             (Hneq: laddr1 <> laddr2)
             (Hres1: lockRes tp laddr1 = Some rmap1)
             (Hres2: lockRes tp laddr2 = Some rmap2),
             permMapsDisjoint2 rmap1 rmap2; (*lock's resources are disjoint *)
         no_race:
           forall i laddr (cnti: containsThread tp i) rmap
             (Hres: lockRes tp laddr = Some rmap),
             permMapsDisjoint2 (getThreadR cnti) rmap; (*resources are disjoint
             between threads and locks*)
         (* an address is in the lockres if there is at least one >= Readable
         lock permission - I am writing the weak version where this is required
         only for permissions of threads*)
         (* lock_res_perm: *)
         (*   forall b ofs, *)
         (*     (exists i (cnti: containsThread tp i), *)
         (*         Mem.perm_order' ((getThreadR cnti).2 !! b ofs) Readable) ->  *)
         (*     lockRes tp (b, ofs); *)

         (* if an address is a lock then there can be no data
             permission above non-empty for this address*)
         thread_data_lock_coh:
           forall i (cnti: containsThread tp i),
             (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 (getThreadR cnti).2) /\
             (forall laddr rmap,
                 lockRes tp laddr = Some rmap ->
                 permMapCoherence rmap.1 (getThreadR cnti).2);
         locks_data_lock_coh:
           forall laddr rmap
             (Hres: lockRes tp laddr = Some rmap),
             (forall j (cntj: containsThread tp j),
                 permMapCoherence (getThreadR cntj).1 rmap.2) /\
             (forall laddr' rmap',
                 lockRes tp laddr' = Some rmap' ->
                 permMapCoherence rmap'.1 rmap.2);
         lockRes_valid: lr_valid (lockRes tp) (*well-formed locks*)
       }.
     Definition invariant := invariant'.

     (** Steps*)
     Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
               (Hcompatible: mem_compatible tp m) :
       thread_pool -> mem -> seq mem_event -> Prop :=
     | step_dry :
         forall (tp':thread_pool) c m1 m' (c' : code) ev
           (** Instal the permission's of the thread on non-lock locations*)
           (Hrestrict_pmap: restrPermMap (Hcompatible tid0 cnt).1 = m1)
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt = Krun c)
           (Hcorestep: ev_step Sem genv c m1 ev c' m')
           (** the new data resources of the thread are the ones on the
           memory, the lock ones are unchanged by internal steps*)
           (Htp': tp' = updThread cnt (Krun c') (getCurPerm m', (getThreadR cnt).2)),
           dry_step genv cnt Hcompatible tp' m' ev.

     Definition option_function {A B} (opt_f: option (A -> B)) (x:A): option B:=
       match opt_f with
         Some f => Some (f x)
       | None => None
       end.
     Infix "??" := option_function (at level 80, right associativity).

     Inductive ext_step {isCoarse:bool} (genv:G) {tid0 tp m}
               (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
       thread_pool -> mem -> sync_event -> Prop :=
     | step_acquire :
         forall (tp' tp'':thread_pool) m0 m1 c m' b ofs
           (pmap : LocksAndResources.lock_info)
           (pmap_tid' : access_map)
           (virtueThread : delta_map * delta_map)
           (Hbounded: if isCoarse then
                        ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                          sub_map virtueThread.2 (getMaxPerm m).2)
                      else
                        True ),
           let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                  computeMap (getThreadR cnt0).2 virtueThread.2) in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: at_external Sem c = Some (LOCK, Vptr b ofs::nil))
             (** install the thread's permissions on lock locations*)
             (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
             (** To acquire the lock the thread must have [Readable] permission on it*)
             (Haccess: Mem.range_perm m0 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Readable)
             (** check if the lock is free*)
             (Hload: Mem.load Mint32 m0 b (Int.intval ofs) = Some (Vint Int.one))
             (** set the permissions on the lock location equal to the max permissions on the memory*)
             (Hset_perm: setPermBlock (Some Writable)
                                       b (Int.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
             (Hlt': permMapLt pmap_tid' (getMaxPerm m))
             (Hrestrict_pmap: restrPermMap Hlt' = m1)
             (** acquire the lock*)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
             (HisLock: lockRes tp (b, Int.intval ofs) = Some pmap)
             (Hangel1: permMapJoin pmap.1 (getThreadR cnt0).1 newThreadPerm.1)
             (Hangel2: permMapJoin pmap.2 (getThreadR cnt0).2 newThreadPerm.2)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) newThreadPerm)
             (** acquiring the lock leaves empty permissions at the resource pool*)
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) (empty_map, empty_map)),
             ext_step genv cnt0 Hcompat tp'' m'
                      (acquire (b, Int.intval ofs)
                               (Some virtueThread))

     | step_release :
         forall (tp' tp'':thread_pool) m0 m1 c m' b ofs virtueThread virtueLP pmap_tid' rmap
           (Hbounded: if isCoarse then
                        ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                          sub_map virtueThread.2 (getMaxPerm m).2)
                      else
                        True )
           (HboundedLP: if isCoarse then
                        ( map_empty_def virtueLP.1 /\
                          map_empty_def virtueLP.2 /\
                          sub_map virtueLP.1.2 (getMaxPerm m).2 /\
                          sub_map virtueLP.2.2 (getMaxPerm m).2)
                      else
                        True ),
           let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                 computeMap (getThreadR cnt0).2 virtueThread.2) in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: at_external Sem c =
                            Some (UNLOCK, Vptr b ofs::nil))
             (** install the thread's permissions on lock locations *)
             (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
             (** To acquire the lock the thread must have [Readable] permission on it*)
             (Haccess: Mem.range_perm m0 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Readable)
             (Hload: Mem.load Mint32 m0 b (Int.intval ofs) = Some (Vint Int.zero))
             (** set the permissions on the lock location equal to the max permissions on the memory*)
             (Hset_perm: setPermBlock (Some Writable)
                                      b (Int.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
             (Hlt': permMapLt pmap_tid' (getMaxPerm m))
             (Hrestrict_pmap: restrPermMap Hlt' = m1)
             (** release the lock *)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
             (HisLock: lockRes tp (b, Int.intval ofs) = Some rmap)
             (** And the lock is taken*)
             (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
             (Hangel1: permMapJoin newThreadPerm.1 virtueLP.1 (getThreadR cnt0).1)
             (Hangel2: permMapJoin newThreadPerm.2 virtueLP.2 (getThreadR cnt0).2)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef)
                                    (computeMap (getThreadR cnt0).1 virtueThread.1,
                                     computeMap (getThreadR cnt0).2 virtueThread.2))
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) virtueLP),
             ext_step genv cnt0 Hcompat tp'' m'
                      (release (b, Int.intval ofs)
                               (Some virtueLP))
     | step_create :
         forall (tp_upd tp':thread_pool) c b ofs arg virtue1 virtue2
           (Hbounded: if isCoarse then
                        ( sub_map virtue1.1 (getMaxPerm m).2 /\
                          sub_map virtue1.2 (getMaxPerm m).2)
                      else
                        True )
             (Hbounded_new: if isCoarse then
                        ( sub_map virtue2.1 (getMaxPerm m).2 /\
                          sub_map virtue2.2 (getMaxPerm m).2)
                      else
                        True ),
           let threadPerm' := (computeMap (getThreadR cnt0).1 virtue1.1,
                               computeMap (getThreadR cnt0).2 virtue1.2) in
           let newThreadPerm := (computeMap empty_map virtue2.1,
                                 computeMap empty_map virtue2.2) in
           forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c = Some (CREATE, Vptr b ofs::arg::nil))
           (** we do not need to enforce the almost empty predicate on thread
           spawn as long as it's considered a synchronizing operation *)
           (Hangel1: permMapJoin newThreadPerm.1 threadPerm'.1 (getThreadR cnt0).1)
           (Hangel2: permMapJoin newThreadPerm.2 threadPerm'.2 (getThreadR cnt0).2)
           (Htp_upd: tp_upd = updThread cnt0 (Kresume c Vundef) threadPerm')
           (Htp': tp' = addThread tp_upd (Vptr b ofs) arg newThreadPerm),
             ext_step genv cnt0 Hcompat tp' m
                      (spawn (b, Int.intval ofs)
                             (Some (getThreadR cnt0, virtue1)) (Some virtue2))


     | step_mklock :
         forall  (tp' tp'': thread_pool) m1 c m' b ofs pmap_tid',
           let: pmap_tid := getThreadR cnt0 in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: at_external Sem c = Some (MKLOCK, Vptr b ofs::nil))
             (** install the thread's data permissions*)
             (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m1)
             (** To create the lock the thread must have [Writable] permission on it*)
             (Hfreeable: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Writable)
             (** lock is created in acquired state*)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
             (** The thread's data permissions are set to Nonempty*)
             (Hdata_perm: setPermBlock
                            (Some Nonempty)
                            b
                            (Int.intval ofs)
                            pmap_tid.1
                            LKSIZE_nat = pmap_tid'.1)
             (** thread lock permission is increased *)
             (Hlock_perm: setPermBlock
                            (Some Writable)
                            b
                            (Int.intval ofs)
                            pmap_tid.2
                            LKSIZE_nat = pmap_tid'.2)
             (** Require that [(b, Int.intval ofs)] was not a lock*)
             (HlockRes: lockRes tp (b, Int.intval ofs) = None)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
             (** the lock has no resources initially *)
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) (empty_map, empty_map)),
             ext_step genv cnt0 Hcompat tp'' m' (mklock (b, Int.intval ofs))

     | step_freelock :
         forall  (tp' tp'': thread_pool) c b ofs pmap_tid' m1 pdata rmap
           (Hbounded: if isCoarse then
                        ( bounded_maps.bounded_nat_func' pdata LKSIZE_nat)
                      else
                        True ),
             let: pmap_tid := getThreadR cnt0 in
           forall
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c = Some (FREE_LOCK, Vptr b ofs::nil))
           (** If this address is a lock*)
           (His_lock: lockRes tp (b, (Int.intval ofs)) = Some rmap)
           (** And the lock is taken *)
           (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To free the lock the thread must have at least Writable on it*)
           (Hfreeable: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Writable)
           (** lock permissions of the thread are dropped to empty *)
           (Hlock_perm: setPermBlock
                          None
                          b
                          (Int.intval ofs)
                          pmap_tid.2
                          LKSIZE_nat = pmap_tid'.2)
           (** data permissions are computed in a non-deterministic way *)
           (Hneq_perms: forall i,
                 (0 <= Z.of_nat i < LKSIZE)%Z ->
                 Mem.perm_order'' (pdata (S i)) (Some Writable)
           )
           (*Hpdata: perm_order pdata Writable*)
           (Hdata_perm: setPermBlock_var (*=setPermBlockfunc*)
                          pdata
                          b
                          (Int.intval ofs)
                          pmap_tid.1
                          LKSIZE_nat = pmap_tid'.1)
           (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
           (Htp'': tp'' = remLockSet tp' (b, Int.intval ofs)),
           ext_step genv cnt0 Hcompat  tp'' m (freelock (b, Int.intval ofs))
     | step_acqfail :
         forall  c b ofs m1
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c = Some (LOCK, Vptr b ofs::nil))
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To acquire the lock the thread must have [Readable] permission on it*)
           (Haccess: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Readable)
           (** Lock is already acquired.*)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
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
        eapply (cntUpdate (Krun c') (getCurPerm m', (getThreadR cnt)#2) cntj) in cntj'.
        exists cntj'.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c'.
          rewrite gssThreadCode; reflexivity.
        + exists q.
          rewrite gsoThreadCode; auto.
      - intros [cntj' [ q' running]].
        inversion H; subst.
        assert (cntj:=cntj').
        eapply cntUpdate' with(c0:=Krun c')(p:=(getCurPerm m', (getThreadR cnt)#2)) in cntj; eauto.
        exists cntj.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c.
          rewrite <- Hcode.
          f_equal.
          apply cnt_irr.
        + exists q'.
          rewrite gsoThreadCode in running; auto.
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
        * exists (cntUpdateL _ _
                        (cntUpdate (Kresume c Vundef)
                                   newThreadPerm
                                   _ cntj)), q.
          rewrite gLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists ( (cntUpdateL _ _
                          (cntUpdate (Kresume c Vundef)
                                     (computeMap (getThreadR cnt)#1 virtueThread#1,
                                      computeMap (getThreadR cnt)#2 virtueThread#2)
                                     _ cntj))), q.
          rewrite gLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists (cntAdd _ _ _
                    (cntUpdate (Kresume c Vundef)
                               threadPerm'
                               _ cntj)), q.
          erewrite gsoAddCode . (*i? *)
          rewrite gsoThreadCode; assumption.
          eapply cntUpdate. eauto.
        * exists ( (cntUpdateL _ _
                          (cntUpdate (Kresume c Vundef)
                                     pmap_tid'
                                     _ cntj))), q.
          rewrite gLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists ( (cntRemoveL _
                          (cntUpdate (Kresume c Vundef)
                                     pmap_tid'
                                     _ cntj))), q.
          rewrite gRemLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists cntj, q; assumption.
    - intros [cntj [ q running]].
      destruct (NatTID.eq_tid_dec i j).
      + subst j. generalize running; clear running.
        inversion H; subst;
          try rewrite gLockSetCode;
          try rewrite gRemLockSetCode;
          try rewrite gssThreadCode;
          try solve[intros HH; inversion HH].
        { (*addthread*)
          assert (cntj':=cntj).
          eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
          * erewrite gsoAddCode; eauto.
            subst; rewrite gssThreadCode; intros AA; inversion AA.
          * erewrite gssAddCode . intros AA; inversion AA.
            assumption. }
          { (*AQCUIRE*)
            replace cntj with cnt by apply cnt_irr.
            rewrite Hcode; intros HH; inversion HH. }
      + generalize running; clear running.
        inversion H; subst;
        try erewrite <- age_getThreadCode;
          try rewrite gLockSetCode;
          try rewrite gRemLockSetCode;
          try (rewrite gsoThreadCode; [|auto]);
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
            [subst; rewrite gssThreadCode; intros AA; inversion AA|].
          rewrite gsoThreadCode; auto.
          exists HH, q; assumption.
        * erewrite gssAddCode . intros AA; inversion AA.
          assumption.



          Grab Existential Variables.
          eauto. eauto. eauto.
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
           (*Hinv: invariant tp*)
           (Hcode: getThreadC cnt = Krun c)
           (Hcant: halted Sem c),
           threadHalted' cnt.

    Definition threadHalted: forall {tid0 ms},
         containsThread ms tid0 -> Prop:= @threadHalted'.


   (* Lemma updCinvariant': forall {tid} ds c (cnt: containsThread ds tid),
         invariant (updThreadC cnt c) <-> invariant ds.
           split.
           { intros INV; inversion INV.
             constructor.
             - generalize no_race; unfold race_free.
               simpl. intros.
               apply no_race0; auto.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption. }

           { intros INV; inversion INV.
             constructor.
             - generalize no_race; unfold race_free.
               simpl. intros.
               apply no_race0; auto.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption. }
     Qed. *)


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


     Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

     Definition initial_machine pmap c :=
       ThreadPool.mk
         one_pos
         (fun _ =>  Krun c)
         (fun _ => (pmap, empty_map)) (*initially there are no locks*)
         empty_lset.


     Definition init_mach (pmap : option RES.res) (genv:G)
                (v:val)(args:list val):option thread_pool :=
       match initial_core Sem 0 genv v args with
       | Some c =>
         match pmap with
         | Some pmap => Some (initial_machine pmap.1 c)
         | None => None
         end
       | None => None
       end.

     Module DryMachineLemmas.


       (*TODO: This lemma should probably be moved. *)
       Lemma threads_canonical:
         forall ds m i (cnt:ThreadPool.containsThread ds i),
           mem_compatible ds m ->
           isCanonical (ThreadPool.getThreadR cnt).1 /\
           isCanonical (ThreadPool.getThreadR cnt).2.
             intros.
             destruct (compat_th H cnt);
               eauto using canonical_lt.
       Qed.
       (** most of these lemmas are in DryMachinLemmas*)

       (** *Invariant Lemmas*)

       (** ** Updating the machine state**)
        (* Manny invaraint lemmas were removed from here. *)
     End DryMachineLemmas.



    (** *More Properties of halted thread*)
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
      rewrite gsoThreadCode; auto;
      erewrite <- age_getThreadCode; eauto.
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
        try erewrite <- age_getThreadCode;
          try rewrite gLockSetCode;
          try rewrite gRemLockSetCode;
          try erewrite gsoAddCode; eauto;
          try rewrite gsoThreadCode; try eassumption.
        { (*AQCUIRE*)
            replace cnt' with cnt0 by apply cnt_irr;
          exact Hcode. }
    - destruct (NatTID.eq_tid_dec i j).
      + subst j.
        inversion H; subst;
        match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
            try erewrite <- age_getThreadCode in H;
              try rewrite gLockSetCode in H;
              try rewrite gRemLockSetCode in H;
              try erewrite gsoAddCode in H; eauto;
              try rewrite gssThreadCode in H;
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
            try erewrite <- age_getThreadCode in H;
              try rewrite gLockSetCode in H;
              try rewrite gRemLockSetCode in H;
              try erewrite gsoAddCode in H; eauto;
              try rewrite gsoThreadCode in H;
              try solve[inversion H]; eauto
        end.
        { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
          exact Hcode. }

        Grab Existential Variables.
        eauto. eauto. eauto.
  Qed.


  End DryMachineShell.

End Concur.
