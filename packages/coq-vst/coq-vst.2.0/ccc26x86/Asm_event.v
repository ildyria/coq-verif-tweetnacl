Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Floats.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.
Require Import VST.ccc26x86.Locations.
(*Require Import Stacklayout.*)
Require Import VST.ccc26x86.Conventions.

Require Import VST.ccc26x86.Asm.
(*LENB: In CompComp, we used a modified Asm.v, called Asm.comp.v*)

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.val_casted.
Require Import VST.ccc26x86.BuiltinEffects.
Require Import VST.ccc26x86.load_frame.
Require Import VST.sepcomp.event_semantics.
Require Import VST.ccc26x86.Asm_coop.

Require Import List. Import ListNotations.
(*
Notation SP := ESP (only parsing).

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

Inductive load_frame: Type :=
| mk_load_frame:
    forall (sp: block)           (**r pointer to argument frame *)
           (retty: option typ),  (**r return type *)
    load_frame.
*)

Section ASM_EV.
(*Variable hf : I64Helpers.helper_functions.*)

Definition drf_instr (ge:genv) (c: code) (i: instruction) (rs: regset) (m: mem)
           : option (list mem_event)  :=
  match i with
  | Pfstps_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat32 (rs ST0))]
                  | _ => None
                 end
  | Pfstpl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat64 (rs ST0))]
                  | _ => None
                 end
  | Pmovss_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat32 (rs r1))]
                  | _ => None
                 end
  | Pmov_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mint32 (rs r1))]
                  | _ => None
                 end
  | Pmov_mr_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Many32 (rs r1))]
                  | _ => None
                 end
  | Pmovsd_mf a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mfloat64 (rs r1))]
                  | _ => None
                 end
  | Pmovsd_mf_a a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs)  (encode_val Many64 (rs r1))]
                  | _ => None
                 end
  | Pmovb_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mint8unsigned (rs r1))]
                  | _ => None
                 end
  | Pmovw_mr a r1 => match eval_addrmode ge a rs with
                    Vptr b ofs => Some [Write b (Int.unsigned ofs) (encode_val Mint16unsigned (rs r1))]
                  | _ => None
                 end

  | Pmov_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint32) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovsd_fm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat64) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat64) bytes]
                                  | None => None
                                  end
                  | _ => None
                 end
  | Pmovss_fm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pfldl_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat64) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat64) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pflds_m a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mfloat32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mfloat32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovzb_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint8unsigned) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint8unsigned) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsb_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint8signed) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint8signed) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovzw_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint16unsigned) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint16unsigned) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsw_rm rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Mint16signed) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Mint16signed) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmov_rm_a rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Many32) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Many32) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pmovsd_fm_a rd a => match eval_addrmode ge a rs with
                    Vptr b ofs => match Mem.loadbytes m b (Int.unsigned ofs) (size_chunk Many64) with
                                    Some bytes => Some [Read b (Int.unsigned ofs) (size_chunk Many64) bytes]
                                  | None => None
                                  end
                  | _ => None
                  end
  | Pallocframe sz ofs_ra ofs_link =>
      let (m1, stk) := Mem.alloc m 0 sz in
      let sp := Vptr stk Int.zero in
      match Mem.storev Mint32 m1 (Val.add sp (Vint ofs_link)) rs#ESP with
      | None => None
      | Some m2 =>
          match Mem.storev Mint32 m2 (Val.add sp (Vint ofs_ra)) rs#RA with
          | None => None
          | Some m3 => Some [Alloc stk 0 sz;
                             Write stk (Int.unsigned ofs_link) (encode_val Mint32 (rs ESP));
                             Write stk (Int.unsigned ofs_ra) (encode_val Mint32 (rs RA))]
          end
      end
  | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_ra)) with
      | None => None
      | Some ra =>
          match Mem.loadv Mint32 m (Val.add rs#ESP (Vint ofs_link)) with
          | None => None
          | Some sp =>
              match rs#ESP with
              | Vptr stk ofs =>
                  match Mem.free m stk 0 sz with
                  | None => None
                  | Some m' => match (Val.add rs#ESP (Vint ofs_ra)), (Val.add rs#ESP (Vint ofs_link)) with
                                Vptr b1 ofs1, Vptr b2 ofs2 =>
                                  match Mem.loadbytes m b1 (Int.unsigned ofs1) (size_chunk Mint32), Mem.loadbytes m b2 (Int.unsigned ofs2) (size_chunk Mint32)
                                  with Some bytes1, Some bytes2=>
                                     Some [Read b1 (Int.unsigned ofs1) (size_chunk Mint32) bytes1;
                                           Read b2 (Int.unsigned ofs2) (size_chunk Mint32) bytes2;
                                           Free [(stk, 0, sz)]]
                                   | _, _ => None
                                  end
                              | _, _ => None
                              end
                  end
              | _ => None
              end
          end
      end
(*  | Pbuiltin ef args res => EmptyEffect
(*     (BuiltinEffect ge ef (decode_longs (sig_args (ef_sig ef)) (map rs args)) m)*)
(*  | Pannot ef args =>
      EmptyEffect *)*)
  | _ => Some [Free nil]
  end.

Lemma store_stack_ev_elim m sp ty ofs v m' (SS: store_stack m sp ty ofs v = Some m'):
  exists b z, sp =Vptr b z /\
  ev_elim m [Write b (Int.unsigned (Int.add z ofs)) (encode_val (chunk_of_type ty) v)] m'.
Proof.
  destruct sp; try discriminate. unfold store_stack in SS.
  exists b, i; split; trivial.
  apply Mem.store_storebytes in SS.
  econstructor. split. eassumption. constructor.
Qed.

Fixpoint store_args_ev_rec sp ofs args tys : option (list mem_event) :=
  match tys, args with
    | nil, nil => Some nil
    | ty'::tys',a'::args' =>
      match ty', a' with
        | Tlong, Vlong n =>
           match store_args_ev_rec sp (ofs+2) args' tys' with
             None => None
           | Some tailEvents =>
               Some ((Write sp (Int.unsigned (Int.repr(Stacklayout.fe_ofs_arg + 4*(ofs+1))))
                              (encode_val (chunk_of_type Tint) (Vint (Int64.hiword n)))) ::
                     (Write sp (Int.unsigned (Int.repr(Stacklayout.fe_ofs_arg + 4*ofs)))
                            (encode_val (chunk_of_type Tint) (Vint (Int64.loword n)))) ::
                     tailEvents)
           end
        | Tlong, _ => None
        | _,_ =>
           match store_args_ev_rec sp (ofs+typesize ty') args' tys' with
             None => None
           | Some tailEvents =>
               Some ((Write sp (Int.unsigned (Int.repr (Stacklayout.fe_ofs_arg + 4*ofs))) (encode_val (chunk_of_type ty') a'))
                      :: tailEvents)
           end
      end
    | _, _ => None
  end.

Lemma store_args_ev_elim sp: forall args tys ofs m m' (SA: store_args_rec m sp ofs args tys = Some m'),
  exists T, store_args_ev_rec sp ofs args tys = Some T /\ ev_elim m T m'.
Proof.
induction args; intros tys; destruct tys; simpl; intros; try discriminate.
+ inv SA. exists nil. split. trivial. constructor.
+ destruct t.
  - remember (store_stack m (Vptr sp Int.zero) Tint
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b [z [B EV]]]; inv B.
    rewrite Int.add_zero_l in EV.
    simpl in EV. destruct EV as [mm [SB MM]]; subst m0.
    eexists; split. reflexivity.
    econstructor. split; eassumption.
  - remember (store_stack m (Vptr sp Int.zero) Tfloat
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b [z [B EV]]]; inv B.
    rewrite Int.add_zero_l in EV.
    simpl in EV. destruct EV as [mm [SB MM]]; subst m0.
    eexists; split. reflexivity.
    econstructor. split; eassumption.
  - destruct a; try discriminate.
    remember (store_stack m (Vptr sp Int.zero) Tint
         (Int.repr
            match ofs + 1 with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) (Vint (Int64.hiword i))) as p.
    destruct p; inv SA.
    remember (store_stack m0 (Vptr sp Int.zero) Tint
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) (Vint (Int64.loword i))) as q.
    destruct q; inv H0.
    destruct (IHargs _ _ _ _ H1) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    symmetry in Heqq. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqq) as [b2 [z2 [B2 EV2]]]; inv B2.
    rewrite Int.add_zero_l in EV2.
    simpl in EV2. destruct EV2 as [mm2 [SB2 MM2]]. subst m1. clear - SB1 SB2 EVT.
    eexists; split. reflexivity.
    econstructor. split. apply SB1.
    econstructor. split. apply SB2. assumption.
  - remember (store_stack m (Vptr sp Int.zero) Tsingle
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    eexists; split. reflexivity.
    econstructor. split. apply SB1. assumption.
  - remember (store_stack m (Vptr sp Int.zero) Tany32
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    eexists; split. reflexivity.
    econstructor. split. apply SB1. assumption.
  - remember (store_stack m (Vptr sp Int.zero) Tany64
         (Int.repr
            match ofs with
            | 0 => 0
            | Z.pos y' => Z.pos y'~0~0
            | Z.neg y' => Z.neg y'~0~0
            end) a) as p.
    destruct p; inv SA.
    destruct (IHargs _ _ _ _ H0) as [T [SAT EVT]]. simpl. rewrite SAT.
    symmetry in Heqp. destruct (store_stack_ev_elim _ _ _ _ _ _ Heqp) as [b1 [z1 [B1 EV1]]]; inv B1.
    rewrite Int.add_zero_l in EV1.
    simpl in EV1. destruct EV1 as [mm1 [SB1 MM1]]. subst m0.
    eexists; split. reflexivity.
    econstructor. split. apply SB1. assumption.
Qed.

Definition store_args_events sp args tys := store_args_ev_rec sp 0 args tys.

Lemma AR n: match n with
                  | 0 => 0
                  | Z.pos y' => Z.pos y'~0~0
                  | Z.neg y' => Z.neg y'~0~0
                  end = 4*n.
destruct n; simpl; trivial. Qed.

Section EXTCALL_ARG_EVENT.

Inductive extcall_arg_ev (rs: regset) (m: mem): loc -> val -> list mem_event -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg_ev rs m (R r) (rs (preg_of r)) nil
  | extcall_arg_stack: forall ofs v ty bofs bytes chunk b z,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Val.add (rs (IR ESP)) (Vint (Int.repr bofs)) = Vptr b z ->
      chunk = chunk_of_type ty ->
(*      Mem.loadv chunk m (Vptr b z) = Some v ->
      extcall_arg_ev rs m (S Outgoing ofs ty) v [Read b (Int.unsigned z) (size_chunk chunk) (encode_val chunk v)].*)
      (*(align_chunk (chunk_of_type ty) (Int.unsigned z)) ->*)
      (align_chunk (chunk_of_type ty) | Int.unsigned z) -> (*(Int.add i (Int.repr (4 * ofs))))*)
      Mem.loadbytes m b (Int.unsigned z) (size_chunk chunk) = Some bytes ->
      v= decode_val chunk bytes ->
      extcall_arg_ev rs m (S Outgoing ofs ty) v [Read b (Int.unsigned z) (size_chunk chunk) bytes].

Lemma extcall_arg_extcall_arg_ev rs m l u (EA:extcall_arg rs m l u) : exists T, extcall_arg_ev rs m l u T.
Proof.
  inv EA.
+ exists nil; constructor.
+ remember (rs ESP) as p; destruct p; inv H0.
  destruct (Mem.load_loadbytes _ _ _ _ _ H1) as [bytes [Bytes U]]. rewrite AR in *.
  destruct (Mem.load_valid_access _ _ _ _ _ H1) as [ ALGN].
  eexists; econstructor; try eassumption; try rewrite <- Heqp; reflexivity.
Qed.

Lemma extcall_arg_ev_extcall_arg rs m l u T (EA:extcall_arg_ev rs m l u T): extcall_arg rs m l u.
Proof.
  inv EA.
+ constructor.
+ remember (rs ESP) as p; destruct p; inv H0. rewrite AR in *.
  econstructor. reflexivity. rewrite <- Heqp. simpl. rewrite AR.
  erewrite Mem.loadbytes_load; try reflexivity; eassumption.
Qed.

Lemma extcall_arg_ev_determ rs m l u T (EAV:extcall_arg_ev rs m l u T) T' (EAV':extcall_arg_ev rs m l u T'): T=T'.
Proof. inv EAV; inv EAV'; trivial. rewrite H5 in H0; inv H0. rewrite H8 in H3; inv H3. trivial. Qed.

Inductive extcall_arg_pair_ev (rs: regset) (m: mem): rpair loc -> val -> list mem_event -> Prop :=
  | extcall_arg_ev_one: forall l v T,
      extcall_arg_ev rs m l v T ->
      extcall_arg_pair_ev rs m (One l) v T
  | extcall_arg_ev_twolong: forall hi lo vhi vlo T1 T2,
      extcall_arg_ev rs m hi vhi T1 ->
      extcall_arg_ev rs m lo vlo T2 ->
      extcall_arg_pair_ev rs m (Twolong hi lo) (Val.longofwords vhi vlo) (T1++T2).


Inductive extcall_arguments_ev_aux: regset -> mem -> list (rpair loc) -> list val -> list mem_event -> Prop :=
  extcall_arguments_ev_nil: forall rs m, extcall_arguments_ev_aux rs m nil nil nil
| extcall_arguments_ev_cons: forall rs m l locs v T1 vl T2 ,
                         extcall_arg_pair_ev rs m l v T1 ->
                         extcall_arguments_ev_aux rs m locs vl T2 ->
                         extcall_arguments_ev_aux rs m (l::locs) (v::vl) (T1++T2).

Definition extcall_arguments_ev (rs:regset) (m: mem) (sg:signature) (args: list val) (T: list mem_event): Prop :=
  extcall_arguments_ev_aux rs m (loc_arguments sg) args T.

Lemma extcall_arguments_extcall_arguments_ev rs m sg args:
      extcall_arguments rs m sg args -> exists T, extcall_arguments_ev rs m sg args T.
Proof.
unfold extcall_arguments, extcall_arguments_ev. remember (loc_arguments sg) as locs. clear Heqlocs.
intros LF; induction LF.
+ exists nil; constructor.
+ destruct IHLF as [T2 HT2].
  destruct H.
  - destruct (extcall_arg_extcall_arg_ev _ _ _ _ H) as [T1 HT1].
    exists (T1++T2). econstructor. econstructor. eassumption. eassumption.
  - destruct (extcall_arg_extcall_arg_ev _ _ _ _ H) as [Thi Hhi].
    destruct (extcall_arg_extcall_arg_ev _ _ _ _ H0) as [Tlo Hlo]. simpl.
    exists ((Thi++Tlo)++T2). econstructor. econstructor. eassumption. eassumption. eassumption.
Qed.

Lemma extcall_arg_pair_ev_determ rs m: forall l v T1 (HT1: extcall_arg_pair_ev rs m l v T1)
      T2 (HT2: extcall_arg_pair_ev rs m l v T2), T1=T2.
Proof. intros.
  induction HT1.
  + inv HT2. eapply extcall_arg_ev_determ; eassumption.
  + inv HT2.
    inv H.
    - inv H4. inv H0. inv H6. trivial. inv H6. rewrite H7 in H1. inv H1.
      rewrite H5 in H10. inv H10. trivial.
    - inv H4. rewrite H9 in H2. inv H2. rewrite H8 in H12. inv H12. f_equal.
      inv H0.
      * inv H6; trivial.
      * inv H6. rewrite H1 in H10. inv H10. rewrite H14 in H5. inv H5. trivial.
Qed.

Lemma extcall_arguments_ev_aux_determ rs m: forall locs args T (EA: extcall_arguments_ev_aux rs m locs args T)
      T' (EA': extcall_arguments_ev_aux rs m locs args T'), T=T'.
Proof.
  induction 1; simpl; intros; inv EA'; trivial. f_equal.
  eapply extcall_arg_pair_ev_determ; eassumption.
  eauto.
Qed.

Lemma extcall_arguments_ev_determ rs m sg args T (EA: extcall_arguments_ev rs m sg args T)
      T' (EA': extcall_arguments_ev rs m sg args T'): T=T'.
Proof. eapply extcall_arguments_ev_aux_determ; eassumption. Qed.

Lemma extcall_arguments_ev_extcall_arguments rs m sg args T:
      extcall_arguments_ev rs m sg args T -> extcall_arguments rs m sg args.
Proof.
unfold extcall_arguments, extcall_arguments_ev. remember (loc_arguments sg) as locs. clear Heqlocs.
intros LF; induction LF.
+ constructor.
+ inv H.
  - apply extcall_arg_ev_extcall_arg in H0. econstructor; eauto. constructor. trivial.
  - apply extcall_arg_ev_extcall_arg in H0. apply extcall_arg_ev_extcall_arg in H1.
    econstructor; eauto. constructor; trivial.
Qed.

Lemma extcall_arg_ev_elim rs m : forall l v T (EA: extcall_arg_ev rs m l v T), ev_elim m T m.
Proof. induction 1; repeat constructor; eauto. Qed.

Lemma extcall_arg_ev_elim_strong rs m : forall l v T (EA: extcall_arg_ev rs m l v T),
      ev_elim m T m /\ (forall mm mm', ev_elim mm T mm' -> mm'=mm /\ extcall_arg_ev rs mm l v T).
Proof.
 induction 1.
+ split.
  - constructor.
  - intros. inv H. split. trivial. constructor.
+ split.
  - repeat constructor; eauto.
  - intros. inv H4. inv H5. inv H1.
    split. trivial.
    econstructor; try eassumption; reflexivity.
Qed.

Lemma extcall_arguments_ev_aux_elim rs m:
      forall l args T (EA: extcall_arguments_ev_aux rs m l args T), ev_elim m T m.
Proof. induction 1.
+ constructor.
+ inv H.
  - apply extcall_arg_ev_elim in H0. eapply ev_elim_app; eassumption.
  - apply extcall_arg_ev_elim in H0. apply extcall_arg_ev_elim in H1.
    rewrite <- app_assoc. eapply ev_elim_app. eassumption. eapply ev_elim_app; eassumption.
Qed.

Lemma extcall_arguments_ev_aux_elim_strong rs m:
      forall l args T (EA: extcall_arguments_ev_aux rs m l args T),
      ev_elim m T m /\ (forall mm mm', ev_elim mm T mm' -> mm'=mm /\ extcall_arguments_ev_aux rs mm l args T).
Proof. induction 1.
+ split.
  - constructor.
  - intros. inv H. split; trivial. constructor.
+ destruct IHEA as [IH1 IH2].
  split.
  - inv H.
    * apply extcall_arg_ev_elim in H0. eapply ev_elim_app; eassumption.
    * apply extcall_arg_ev_elim in H0. apply extcall_arg_ev_elim in H1.
      rewrite <- app_assoc. eapply ev_elim_app. eassumption. eapply ev_elim_app; eassumption.
  - intros. (* destruct (extcall_arg_ev_elim_strong _ _ _ _ _ H) as [E1 HT1].*)
    apply ev_elim_split in H0; destruct H0 as [m2 [EV1 EV2]].
    destruct (IH2 _ _ EV2) as [MM EA2]; subst; clear IH2.
(*    destruct (HT1 _ _ EV1) as [MM EA1]; subst.
    split. trivial.
    constructor; eassumption.*)
    destruct H.
    * destruct (extcall_arg_ev_elim_strong _ _ _ _ _ H) as [E1 HT1].
      destruct (HT1 _ _ EV1) as [MM EA1]; subst.
      split. trivial.
      econstructor. econstructor. eassumption. eassumption.
    * destruct (extcall_arg_ev_elim_strong _ _ _ _ _ H) as [Ehi Hhi]; clear H.
      destruct (extcall_arg_ev_elim_strong _ _ _ _ _ H0) as [Elo Hlo]; clear H0.
      apply ev_elim_split in EV1; destruct EV1 as [m3 [EV1 EV3]].
      destruct (Hhi _ _ EV1) as [MHI EAhi]; subst; clear Hhi.
      destruct (Hlo _ _ EV3) as [MLO EAlo]; subst; clear Hlo.
      split. trivial.
      econstructor. econstructor. eassumption. eassumption. eassumption.
Qed.

End EXTCALL_ARG_EVENT.

Section EVAL_BUILTIN_ARG_EV.

Variable A: Type.
Variable ge: Senv.t.
Variable e: A -> val.
Variable sp: val.
Variable m: mem.

Inductive eval_builtin_arg_ev: builtin_arg A -> val -> list mem_event -> Prop :=
  | eval_BA_ev: forall x,
      eval_builtin_arg_ev (BA x) (e x) nil
  | eval_BA_ev_int: forall n,
      eval_builtin_arg_ev (BA_int n) (Vint n) nil
  | eval_BA_ev_long: forall n,
      eval_builtin_arg_ev (BA_long n) (Vlong n) nil
  | eval_BA_ev_float: forall n,
      eval_builtin_arg_ev (BA_float n) (Vfloat n) nil
  | eval_BA_ev_single: forall n,
      eval_builtin_arg_ev (BA_single n) (Vsingle n) nil
  | eval_BA_ev_loadstack: forall chunk ofs v b z bytes,
      Mem.loadv chunk m (Val.add sp (Vint ofs)) = Some v ->
      (align_chunk chunk | (Int.unsigned z)) ->
      Mem.loadbytes m b (Int.unsigned z) (size_chunk chunk) = Some bytes ->
      v= decode_val chunk bytes ->
      Val.add sp (Vint ofs) = Vptr b z ->
      eval_builtin_arg_ev (BA_loadstack chunk ofs) v [Read b (Int.unsigned z) (size_chunk chunk) bytes]
  | eval_BA_ev_addrstack: forall ofs,
      eval_builtin_arg_ev (BA_addrstack ofs) (Val.add sp (Vint ofs)) nil
  | eval_BA_ev_loadglobal: forall chunk id ofs v b z bytes,
      Mem.loadv chunk m (Senv.symbol_address ge id ofs) = Some v ->
      (align_chunk chunk | (Int.unsigned z)) ->
      Mem.loadbytes m b (Int.unsigned z) (size_chunk chunk) = Some bytes ->
      v= decode_val chunk bytes ->
      Senv.symbol_address ge id ofs = Vptr b z ->
      eval_builtin_arg_ev (BA_loadglobal chunk id ofs) v [Read b (Int.unsigned z) (size_chunk chunk) bytes]
  | eval_BA_ev_addrglobal: forall id ofs,
      eval_builtin_arg_ev (BA_addrglobal id ofs) (Senv.symbol_address ge id ofs) nil
  | eval_BA_ev_splitlong: forall hi lo vhi vlo Thi Tlo,
      eval_builtin_arg_ev hi vhi Thi -> eval_builtin_arg_ev lo vlo Tlo->
      eval_builtin_arg_ev (BA_splitlong hi lo) (Val.longofwords vhi vlo) (Thi++Tlo).

Lemma eval_builtin_arg_ev_determ: forall a v1 T1 (HT1:eval_builtin_arg_ev a v1 T1)
      v2 T2 (HT2:eval_builtin_arg_ev a v2 T2), v1=v2 /\ T1=T2.
Proof.
induction a; intros; inv HT1; inv HT2; try solve [split; trivial].
+ rewrite H11 in H7; inv H7. rewrite H6 in H3; inv H3. split; trivial.
+ rewrite H12 in H8; inv H8. rewrite H7 in H4; inv H4. split; trivial.
+ destruct (IHa1 _ _ H2 _ _ H1); subst.
  destruct (IHa2 _ _ H6 _ _ H4); subst. split; trivial.
Qed.

Lemma eval_builtin_arg_event: forall a v, eval_builtin_arg ge e sp m a v -> exists T, eval_builtin_arg_ev a v T.
Proof.
  induction 1; intros; try solve [eexists; econstructor; try eassumption].
+ assert (B: exists b z, sp = Vptr b z). destruct sp; inv H. exists b, i; trivial.
  destruct B as [b [i SP]]. subst sp. simpl in H.
  destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALIGN].
  destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes [LD V]].
  eexists. econstructor. subst sp; simpl; eassumption. eassumption. eassumption. trivial. subst sp. reflexivity.
+ assert (B: exists b z, (Senv.symbol_address ge id ofs) = Vptr b z). destruct (Senv.symbol_address ge id ofs); inv H. exists b, i; trivial.
  destruct B as [b [i SA]]. rewrite SA in *.
  destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes [LB V]].
  destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
  eexists. econstructor; try eassumption; trivial. rewrite SA; trivial.
+ destruct IHeval_builtin_arg1 as [Thi HThi]. destruct IHeval_builtin_arg2 as [Tlo HTlo].
  eexists. econstructor; eassumption.
Qed.

Lemma eval_builtin_arg_event_inv: forall a v T, eval_builtin_arg_ev a v T -> eval_builtin_arg ge e sp m a v.
Proof. induction 1; intros; solve [econstructor; try eassumption]. Qed.

Inductive eval_builtin_args_ev: list (builtin_arg A) -> list val -> list mem_event -> Prop :=
  eval_builtin_args_ev_nil: eval_builtin_args_ev nil nil nil
| eval_builtin_args_ev_cons: forall a v T1 al vl T2 ,
                         eval_builtin_arg_ev a v T1 ->
                         eval_builtin_args_ev al vl T2 ->
                         eval_builtin_args_ev (a::al) (v::vl) (T1++T2).

Lemma eval_builtin_args_ev_determ: forall al vl1 T1 (HA1: eval_builtin_args_ev al vl1 T1)
      vl2 T2 (HA2: eval_builtin_args_ev al vl2 T2), vl1=vl2 /\ T1=T2.
Proof.
induction al; intros; inv HA1; inv HA2.
+ split; trivial.
+ destruct (IHal _ _ H6 _ _ H4); subst.
  destruct (eval_builtin_arg_ev_determ  _ _ _ H2 _ _ H1); subst.
  split; trivial.
Qed.

Lemma eval_builtin_args_eval_builtin_args_ev: forall al vl, eval_builtin_args ge e sp m al vl ->
  exists T, eval_builtin_args_ev al vl T.
Proof.
  induction 1.
+ eexists; econstructor.
+ destruct IHlist_forall2 as [T2 HT2].
  destruct (eval_builtin_arg_event _ _ H) as [T1 HT1].
  eexists; econstructor; eassumption.
Qed.

Lemma eval_builtin_args_ev_eval_builtin_args: forall al vl T, eval_builtin_args_ev al vl T ->
  eval_builtin_args ge e sp m al vl.
Proof.
  induction 1.
+ econstructor.
+ apply eval_builtin_arg_event_inv in H. econstructor; eassumption.
Qed.

End EVAL_BUILTIN_ARG_EV.

Lemma eval_builtin_arg_ev_elim_strong {A} ge (rs: A -> val) sp m a v T (EV: eval_builtin_arg_ev A ge rs sp m a v T):
  ev_elim m T m /\
  (forall mm mm', ev_elim mm T mm' -> mm'=mm /\ eval_builtin_arg_ev A ge rs sp mm a v T).
Proof.
  induction EV.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split.
  - constructor; trivial. constructor.
  - intros mm mm' MM; inv MM; split.
    * inv H5; trivial.
    * inv H5. rewrite H3 in *.
      destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes2 [LB2 V2]]. rewrite LB2 in H1; inv H1.
      destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
      constructor; try eassumption; trivial.
      rewrite H3; simpl. erewrite Mem.loadbytes_load; trivial.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ split.
  - constructor; trivial. constructor.
  - intros mm mm' MM; inv MM; split.
    * inv H5; trivial.
    * inv H5. rewrite H3 in *.
      destruct (Mem.load_loadbytes _ _ _ _ _ H) as [bytes2 [LB2 V2]]. rewrite LB2 in H1; inv H1.
      destruct (Mem.load_valid_access _ _ _ _ _ H) as [_ ALGN].
      constructor; try eassumption; trivial.
      rewrite H3; simpl. erewrite Mem.loadbytes_load; trivial.
+ split. econstructor. intros mm mm' MM; inv MM. split; trivial. econstructor.
+ destruct IHEV1 as [EL1 EStrong1]. destruct IHEV2 as [EL2 EStrong2].
  split. eapply ev_elim_app; eassumption.
  intros. apply ev_elim_split in H; destruct H as [m' [E1 E2]].
  destruct (EStrong1 _ _ E1) as [MT EHi]; subst mm.
  destruct (EStrong2 _ _ E2) as [ML ELo]; subst mm'.
  split; trivial.
  constructor; eassumption.
Qed.

Lemma eval_builtin_args_ev_elim_strong {A} ge (rs: A -> val) sp m al vl T (EV: eval_builtin_args_ev A ge rs sp m al vl T):
  ev_elim m T m /\
  (forall mm mm', ev_elim mm T mm' -> mm'=mm /\ eval_builtin_args_ev A ge rs sp mm al vl T).
Proof.
  induction EV.
+ split. constructor.
  intros mm mm' MM; inv MM; split; trivial. constructor.
+ destruct IHEV as [EV2 HEV2].
  apply eval_builtin_arg_ev_elim_strong in H. destruct H as [EV1 HEV1].
  split. eapply ev_elim_app; eassumption.
  intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [m' [EV1' EV2']].
  destruct (HEV1 _ _ EV1') as [? HE1]; subst.
  destruct (HEV2 _ _ EV2') as [? HE2]; subst.
  split; trivial.
  constructor; trivial.
Qed.

Inductive builtin_event: external_function -> mem -> list val -> list mem_event -> Prop :=
  BE_malloc: forall m n m'' b m'
         (ALLOC: Mem.alloc m (-4) (Int.unsigned n) = (m'', b))
         (ALGN : (align_chunk Mint32 | (-4)))
         (ST: Mem.storebytes m'' b (-4) (encode_val Mint32 (Vint n)) = Some m'),
         builtin_event EF_malloc m [Vint n]
               [Alloc b (-4) (Int.unsigned n); Write b (-4) (encode_val Mint32 (Vint n))]
| BE_free: forall m b lo bytes sz m'
        (POS: Int.unsigned sz > 0)
        (LB : Mem.loadbytes m b (Int.unsigned lo - 4) (size_chunk Mint32) = Some bytes)
        (FR: Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz) = Some m')
        (ALGN : (align_chunk Mint32 | Int.unsigned lo - 4))
        (SZ : Vint sz = decode_val Mint32 bytes),
        builtin_event EF_free m [Vptr b lo]
              [Read b (Int.unsigned lo - 4) (size_chunk Mint32) bytes;
               Free [(b,Int.unsigned lo - 4, Int.unsigned lo + Int.unsigned sz)]]
| BE_memcpy: forall m al bsrc bdst sz bytes osrc odst m'
        (AL: al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
        (POS : sz >= 0)
        (DIV : (al | sz))
        (OSRC : sz > 0 -> (al | Int.unsigned osrc))
        (ODST: sz > 0 -> (al | Int.unsigned odst))
        (RNG: bsrc <> bdst \/
                Int.unsigned osrc = Int.unsigned odst \/
                Int.unsigned osrc + sz <= Int.unsigned odst \/ Int.unsigned odst + sz <= Int.unsigned osrc)
        (LB: Mem.loadbytes m bsrc (Int.unsigned osrc) sz = Some bytes)
        (ST: Mem.storebytes m bdst (Int.unsigned odst) bytes = Some m'),
        builtin_event (EF_memcpy sz al) m [Vptr bdst odst; Vptr bsrc osrc]
              [Read bsrc (Int.unsigned osrc) sz bytes;
               Write bdst (Int.unsigned odst) bytes]
| BE_EFexternal: forall name sg m vargs,
        I64Helpers.is_I64_helperS name sg ->
         builtin_event (EF_external name sg) m vargs []
| BE_EFbuiltin: forall name sg m vargs, is_I64_builtinS name sg ->
         builtin_event (EF_builtin name sg) m vargs [].

Lemma builtin_event_determ ef m vargs T1 (BE1: builtin_event ef m vargs T1) T2 (BE2: builtin_event ef m vargs T2): T1=T2.
inv BE1; inv BE2; simpl in *; trivial.
+ rewrite ALLOC0 in ALLOC; inv ALLOC; trivial.
+ rewrite LB0 in LB; inv LB. rewrite <- SZ in SZ0; inv SZ0. trivial.
+ rewrite LB0 in LB; inv LB; trivial.
Qed.

Inductive asm_ev_step ge : state -> mem -> list mem_event -> state -> mem -> Prop :=
  | asm_ev_step_internal:
      forall b ofs f i rs m rs' m' lf T,
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) (fn_code f) = Some i ->
      exec_instr ge f i rs m = Next rs' m' ->
      drf_instr ge (fn_code f) i rs m = Some T ->
      asm_ev_step ge (State rs lf) m T (State rs' lf) m'
  | asm_ev_step_builtin:
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
      forall b ofs f ef args res rs m vargs t vres rs' m' lf T1 T2
        (*(HFD: helper_functions_declared ge hf)*)
         (NASS: ~ isInlinedAssembly ef)  (*NEW; we don't support inlined assembly yet*),
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      find_instr (Int.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
      eval_builtin_args ge rs (rs ESP) m args vargs ->
      external_call ef ge vargs m t vres m' ->
      ~ observableEF (*hf*) ef ->
      rs' = nextinstr_nf
             (set_res res vres
               (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
      eval_builtin_args_ev _ ge rs (rs ESP) m args vargs T1 ->
      builtin_event ef m vargs T2 ->
      asm_ev_step ge (State rs lf) m (T1++T2) (State rs' lf) m'
  | asm_ev_step_to_external:
      forall b ef args rs m lf T
      (*(HFD: helper_functions_declared ge hf)*),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      extcall_arguments rs m (ef_sig ef) args ->
      extcall_arguments_ev rs m (ef_sig ef) args T ->
      asm_ev_step ge (State rs lf) m T (Asm_CallstateOut ef args rs lf) m

  | asm_ev_step_external: (*really, a helper-step*)
      False -> (*We don't support builtins/helpers/vload/vstore etc yet*)
      forall b callee args res rs m t rs' m' lf T
      (*(HFD: helper_functions_declared ge hf)*)
      (OBS: EFisHelper (*hf*) callee),
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External callee) ->
      extcall_arguments rs m (ef_sig callee) args ->
      external_call callee ge args m t res m' ->
      rs' = (set_pair (loc_external_result (ef_sig callee)) res rs) #PC <- (rs RA) ->
      builtin_event  callee m args T ->
      asm_ev_step ge (Asm_CallstateOut callee args rs lf) m T (State rs' lf) m'
  (*NOTE [loader]*)
  | asm_ev_initialize_call:
      forall m args tys retty m1 stk m2 fb z T
      (*(HFD: helper_functions_declared ge hf)*),
      args_len_rec args tys = Some z ->
      Mem.alloc m 0 (4*z) = (m1, stk) ->
      store_args m1 stk args tys = Some m2 ->
      store_args_events stk args tys = Some T ->
      let rs0 := (Pregmap.init Vundef)
                  #PC <- (Vptr fb Int.zero)
                  #RA <- Vzero
                  # ESP <- (Vptr stk Int.zero) in
      asm_ev_step ge (Asm_CallstateIn fb args tys retty) m (Alloc stk 0 (4*z) :: T)
               (State rs0 (mk_load_frame stk retty)) m2.

Lemma asm_ev_ax1 g (*(HFD: helper_functions_declared g hf)*):
  forall c m T c' m' (EStep:asm_ev_step g c m T c' m'), corestep (Asm_mem_sem (*hf*)) g c m c' m'.
Proof.
 induction 1; try contradiction.
+ destruct i; inv H2;
  try solve[eapply asm_exec_step_internal; try eassumption; reflexivity].
(*+ (*builtin*) eapply asm_exec_step_builtin; eassumption.*)
+ (*step-to_callstateOut*) eapply asm_exec_step_to_external; eassumption.
(*+ (*step_from-callstateOut*) eapply asm_exec_step_external; try eassumption.*)
+ (*loadframe*) eapply asm_exec_initialize_call; try eassumption.
Qed.

Lemma asm_ev_ax2 g: forall c m c' m' (CS:corestep (Asm_mem_sem (*hf*)) g c m c' m'),
   exists T, asm_ev_step g c m T c' m'.
Proof. induction 1; try contradiction.
+ destruct i; inv H2;
  try solve [eexists; eapply asm_ev_step_internal; try eassumption; reflexivity].
  - unfold exec_load in H4.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Many32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - unfold exec_load in H4.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_load. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq, LB. reflexivity.
  - unfold exec_store in H4.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    eexists; eapply asm_ev_step_internal; try eassumption; simpl.
    * unfold exec_store. rewrite <- Heqq, Heqp. trivial.
    * rewrite <- Heqq. reflexivity.
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as alloc; destruct alloc as [m1 stk].
    remember (Mem.store Mint32 m1 stk (Int.unsigned (Int.add Int.zero ofs_link)) (rs ESP)) as p; destruct p; try discriminate.
    remember (Mem.store Mint32 m0 stk (Int.unsigned (Int.add Int.zero ofs_ra)) (rs RA)) as q; destruct q; try discriminate.
    inv H4.
    eexists.
    eapply asm_ev_step_internal; try eassumption; simpl.
    * rewrite <- Heqalloc, <- Heqp, <- Heqq. reflexivity.
    * rewrite <- Heqalloc, <- Heqp, <- Heqq. reflexivity.
  - (*Pfreeframe*)
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as p; destruct p; try discriminate.
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q; destruct q; try discriminate.
    remember (rs ESP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as r; destruct r; try discriminate. inv H4.
    symmetry in Heqp, Heqq. simpl in *.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqq) as [bytes2 [Bytes2 LD2]].
    eexists.
    eapply asm_ev_step_internal; try eassumption; simpl.
    * rewrite <- Heqw in *. simpl.
      rewrite Heqp, Heqq, <- Heqr. trivial.
    * rewrite <- Heqw in *. simpl in *.
      rewrite Heqp, Heqq, <- Heqr, Bytes1, Bytes2. reflexivity.
(*+ (*builtin*)
  exploit eval_builtin_args_eval_builtin_args_ev. eassumption. intros [T HT].
  destruct ef; simpl in *; try solve [elim H4; trivial].
  - exists (T ++ nil).
    eapply asm_ev_step_builtin; try eassumption. simpl; trivial.
    eapply BE_EFexternal. destruct (I64Helpers.is_I64_helperS_dec name sg); trivial. elim H4; trivial.
  - exists (T ++ nil).
    eapply asm_ev_step_builtin; try eassumption. simpl; trivial.
    eapply BE_EFbuiltin. destruct (is_I64_builtinS_dec name sg); trivial. elim H4; trivial.
  - (*malloc*)
    inv H3. destruct (Mem.store_valid_access_3 _ _ _ _ _ _ H7) as [_ ALGN].
    specialize (Mem.store_storebytes _ _ _ _ _ _ H7). intros.
    eexists. eapply asm_ev_step_builtin; try eassumption; simpl; trivial.
    * econstructor; try eassumption.
    * econstructor; eassumption.
  - (*free*)
    inv H3. destruct (Mem.load_valid_access _ _ _ _ _ H6) as [_ ALGN].
    destruct (Mem.load_loadbytes _ _ _ _ _ H6) as [bytes [LB V]].
    eexists. eapply asm_ev_step_builtin; try eassumption; simpl; trivial.
    * econstructor; try eassumption.
    * econstructor; eassumption.
  - (*memcpy*)
    inv H3.
    eexists. eapply asm_ev_step_builtin; try eassumption; simpl; trivial.
    * econstructor; try eassumption.
    * econstructor; eassumption.*)
+ (*step-to_callstateOut*)
   exploit extcall_arguments_extcall_arguments_ev. eassumption. intros [T HT].
   exists T. econstructor; eassumption.
(*+ (*step_from-callstateOut*)
   exists nil.
   econstructor; try eassumption. inv H1.
   destruct callee; simpl in *; try solve [contradiction].
   eapply BE_EFexternal. trivial.
   eapply BE_EFbuiltin. trivial. *)
+ (*loadframe*)
  unfold store_args in H1.
  destruct (store_args_ev_elim _ _ _ _ _ _ H1) as [T [HT EV]].
  eexists. eapply asm_ev_initialize_call; eassumption.
Qed.

Lemma asm_ev_fun g: forall c m T' c' m' T'' c'' m''
    (Estep': asm_ev_step g c m T' c' m') (Estep'': asm_ev_step g c m T'' c'' m''), T' = T''.
Proof. intros.
inv Estep'; inv Estep''; trivial; try contradiction.
+ rewrite H in H6; inv H6. rewrite H0 in H7; inv H7.
  rewrite H1 in H8; inv H8. rewrite H2 in H9; inv H9.
  rewrite H3 in H14; inv H14. trivial.
(*+ rewrite H in H7; inv H7. rewrite H0 in H7; inv H7.
  rewrite H1 in H8; inv H8. simpl in *; discriminate. *)
+ rewrite H in H6; inv H6. rewrite H0 in H7; inv H7.
(*+ rewrite H in H9; inv H9. rewrite H0 in H10; inv H10.
  rewrite H1 in H11; inv H11. simpl in *; discriminate. *)
(*+ rewrite H9 in H; inv H. rewrite H10 in H0; inv H0.
  rewrite H11 in H1; inv H1.
  exploit eval_builtin_args_ev_determ. apply H16. apply H6. intros [Y X]; subst.
  f_equal. eapply builtin_event_determ; eassumption.*)
(*+ rewrite H9 in H; inv H. rewrite H0 in H10; discriminate.*)
+ rewrite H5 in H; inv H. rewrite H0 in H6; discriminate.
(*+ rewrite H5 in H; inv H. rewrite H0 in H6; inv H6.*)
+ rewrite H5 in H; inv H. rewrite H6 in H0; inv H0.
  exploit extcall_arguments_determ. apply H1. apply H7. intros; subst args.
  eapply extcall_arguments_ev_determ; eassumption.
(*+ rewrite H7 in H; inv H. eapply builtin_event_determ; eassumption. *)
+ (*loadframe*)
  rewrite H7 in H; inv H. rewrite H12 in H0; inv H0.
  rewrite H13 in H1; inv H1. rewrite H14 in H2; inv H2. reflexivity.
Qed.

Lemma asm_ev_elim g: forall c m T c' m' (Estep: asm_ev_step g c m T c' m'), ev_elim m T m'.
Proof.
induction 1; intros; try contradiction.
+ destruct i; inv H2; inv H3;
  try solve [eexists; split; reflexivity].
  - unfold exec_load in H5.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_store in H5.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_store in H5.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_load in H5.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - destruct (Val.divu (rs EAX) (rs # EDX <- Vundef r1)); inv H5.
    destruct (Val.modu (rs EAX) (rs # EDX <- Vundef r1)); inv H3.
    eexists; simpl; split; reflexivity.
  - destruct (Val.divs (rs EAX) (rs # EDX <- Vundef r1)); inv H5.
    destruct (Val.mods (rs EAX) (rs # EDX <- Vundef r1)); inv H3.
    eexists; simpl; split; reflexivity.
  - destruct (eval_testcond c rs); inv H5.
    * destruct b0; inv H3; eexists; simpl; split; reflexivity.
    * eexists; simpl; split; reflexivity.
  - unfold goto_label in H5. rewrite H in *.
    destruct (label_pos l 0 (fn_code f)); inv H5.
    eexists; simpl; split; reflexivity.
  - destruct (eval_testcond c rs); inv H5.
    destruct b0; inv H3; try solve [eexists; simpl; split; reflexivity].
    unfold goto_label in H4. rewrite H in *.
    destruct (label_pos l 0 (fn_code f)); inv H4.
    eexists; simpl; split; reflexivity.
  - destruct (eval_testcond c1 rs); inv H5.
    destruct b0; inv H3.
    * destruct (eval_testcond c2 rs); inv H4.
      destruct b0; inv H3; try solve [eexists; simpl; split; reflexivity].
      unfold goto_label in H4. rewrite H in *.
      destruct (label_pos l 0 (fn_code f)); inv H4.
      eexists; simpl; split; reflexivity.
    * destruct (eval_testcond c2 rs); inv H4; try solve [eexists; simpl; split; reflexivity].
  - destruct (rs r); inv H5.
    destruct (list_nth_z tbl (Int.unsigned i)); inv H3.
    unfold goto_label in H4. rewrite H in *.
    destruct (label_pos l 0 (fn_code f)); inv H4.
    eexists; simpl; split; reflexivity.
  - unfold exec_load in H5.
    remember (Mem.loadv Many32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - unfold exec_load in H5.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    constructor; simpl; trivial.
  - unfold exec_store in H5.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    econstructor. split; simpl; trivial. eassumption.
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as a; symmetry in Heqa; destruct a as [m1 stk].
    remember (Mem.store Mint32 m1 stk
         (Int.unsigned (Int.add Int.zero ofs_link))
         (rs ESP)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (Mem.store Mint32 m0 stk (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as q.
    destruct q; try discriminate; symmetry in Heqq. inv H5; inv H4.
    apply Mem.store_storebytes in Heqp.
    apply Mem.store_storebytes in Heqq.
    rewrite Int.add_zero_l in *.
    econstructor. split. eassumption.
    econstructor. split. eassumption.
    econstructor. split. eassumption.
    econstructor.
  - (*Pfreeframe*)
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q.
    destruct q; try discriminate; symmetry in Heqq.
    remember (rs ESP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as t; destruct t; try discriminate.
    inv H5; inv H4; simpl in *.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqq) as [bytes2 [Bytes2 LD2]].
    simpl in *. rewrite Bytes1, Bytes2 in *. inv H3.
    econstructor. trivial.
    econstructor. trivial.
    econstructor. split. simpl. rewrite <- Heqt; trivial.
    econstructor.
(*+ (*builtin*)
  destruct ef; simpl in *; try solve [elim H4; trivial].
  - inv H7.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    eapply ev_elim_app. eassumption.
    (*EFexternal helpers don't change memory - should follow from HFD*)
  - inv H7.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    eapply ev_elim_app. eassumption.
    (*EFbuiltin helpers don't change memory - should follow from HFD*)
  - (*malloc*)
    inv H3; inv H7. rewrite H8 in ALLOC. inv ALLOC.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    apply Mem.store_storebytes in H9.
    eapply ev_elim_app. eassumption.
    econstructor. split. eassumption.
    econstructor. split. eassumption. constructor.
  - (*free*)
    inv H3; inv H7.
    destruct (Mem.load_loadbytes _ _ _ _ _ H8) as [bytes1 [LB1 SZ1]].
    rewrite LB1 in LB; inv LB. rewrite <- SZ1 in SZ; inv SZ.
    rewrite H10 in FR; inv FR.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    eapply ev_elim_app. eassumption.
    econstructor. eassumption.
    econstructor. split. simpl. rewrite H10. reflexivity. constructor.
  - (*memcpy*)
    inv H3; inv H7. rewrite LB in H14; inv H14. rewrite ST in H15; inv H15.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    eapply ev_elim_app. eassumption.
    econstructor. eassumption.
    econstructor. split. eassumption. constructor.*)
+ eapply extcall_arguments_ev_aux_elim; eassumption.
(*+ inv H1.
  destruct callee; simpl in *; try solve [contradiction].
  - inv H3. (*EFexternal helpers don't change memory - should follow from HFD*)
  - inv H3. (*EFbuiltin helpers don't change memory - should follow from HFD*)*)
+ (*loadframe*)
    eexists. split. eassumption.
    destruct (store_args_ev_elim _ _ _ _ _ _ H1) as [TT [HTT EV]].
    unfold store_args_events in H2. rewrite H2 in HTT. inv HTT. trivial.
Qed. (*due to extcall and builtins -- should all follow from HFD*)

Lemma store_args_rec_transfer stk m2 mm': forall args tys m1 n
 (STARGS: store_args_rec m1 stk n args tys = Some m2) TT
 (STARGSEV: store_args_ev_rec stk n args tys = Some TT) x
 (EV: ev_elim x TT mm'), store_args_rec x stk n args tys = Some mm'.
Proof.
 induction args; simpl; intros; destruct tys; try discriminate.
+ inv STARGS. inv STARGSEV. inv EV.  trivial.
+ rewrite AR in *. Opaque Z.mul.
  destruct t.
  - remember (store_args_ev_rec stk (n + typesize Tint) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tint (Int.repr (4*n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp.
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - remember ( store_args_ev_rec stk (n + typesize Tfloat) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tfloat
             (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp.
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - destruct a; try discriminate.
    remember (store_args_ev_rec stk (n + 2) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV]. inv EV. destruct H.
    remember (store_stack m1 (Vptr stk Int.zero) Tint
             (Int.repr
                match n + 1 with
                | 0 => 0
                | Z.pos y' => Z.pos y'~0~0
                | Z.neg y' => Z.neg y'~0~0
                end) (Vint (Int64.hiword i))) as q. destruct q; inv STARGS.
    remember (store_stack m (Vptr stk Int.zero) Tint (Int.repr (4 * n))
         (Vint (Int64.loword i))) as w; destruct w; inv H2.
    symmetry in Heqq, Heqp, Heqw.
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGNhi].
    unfold store_stack in Heqw; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqw) as [_ ALGNlo].
    specialize (IHargs _ _ _ H3 _ Heqp _ H0).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *; simpl in *.
    erewrite Mem.storebytes_store; try eassumption.
    erewrite Mem.storebytes_store; try eassumption.
    rewrite Int.add_zero_l; assumption. rewrite Int.add_zero_l; assumption.
  - remember (store_args_ev_rec stk (n + typesize Tsingle) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tsingle (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp.
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - remember (store_args_ev_rec stk (n + typesize Tany32) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tany32 (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp.
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
  - remember (store_args_ev_rec stk (n + typesize Tany64) args tys) as p; destruct p; inv STARGSEV.
    inv EV. destruct H as [ST EV].
    remember (store_stack m1 (Vptr stk Int.zero) Tany64 (Int.repr (4 * n)) a) as q; destruct q; inv STARGS.
    symmetry in Heqq, Heqp.
    unfold store_stack in Heqq; destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALGN].
    specialize (IHargs _ _ _ H0 _ Heqp _ EV).
    unfold store_stack; simpl. rewrite Int.add_zero_l in *.
    erewrite Mem.storebytes_store; eassumption.
Qed.

Lemma asm_ev_elim_strong g: forall c m T c' m' (Estep: asm_ev_step g c m T c' m'),
      ev_elim m T m' /\ (forall mm mm', ev_elim mm T mm' -> exists cc', asm_ev_step g c mm T cc' mm').
Proof.
induction 1; intros; try contradiction.
+ destruct i; inv H2; inv H3; try solve [split;
        first [eexists; split; reflexivity |
               intros mm mm' EV'; inv EV'; destruct H2 as [FL EV']; inv EV'; inv FL;
                 eexists; econstructor; try eassumption; reflexivity]].
  - (*Pmov_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl. erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmov_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovsd_fm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsd_mf*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovss_fm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovss_mf*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pfldl_m*)
    unfold exec_load in H5.
    remember (Mem.loadv Mfloat64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pfstpl_m*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat64 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pflds_m*)unfold exec_load in H5.
    remember (Mem.loadv Mfloat32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pfstps_m*)
    unfold exec_store in H5.
    remember (Mem.storev Mfloat32 m (eval_addrmode g a rs) (rs ST0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovb_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint8unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial; eassumption.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovw_mr*)
    unfold exec_store in H5.
    remember (Mem.storev Mint16unsigned m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovzb_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint8unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsb_rm*)unfold exec_load in H5.
    remember (Mem.loadv Mint8signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovzw_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint16unsigned m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsw_rm*)
    unfold exec_load in H5.
    remember (Mem.loadv Mint16signed m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pdiv*)
    remember (Val.divu (rs EAX) (rs # EDX <- Vundef r1)) as p; destruct p; inv H5.
    remember (Val.modu (rs EAX) (rs # EDX <- Vundef r1)) as q; destruct q; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqp, <- Heqq; reflexivity.
  - (*Pidiv*)
    remember (Val.divs (rs EAX) (rs # EDX <- Vundef r1)) as p; destruct p; inv H5.
    remember ( Val.mods (rs EAX) (rs # EDX <- Vundef r1)) as q; destruct q; inv H3.
    split.
    * eexists; simpl; split; reflexivity.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; trivial.
      rewrite <- Heqp, <- Heqq; reflexivity.
  - (*Pcmov*)
    remember (eval_testcond c rs) as p; destruct p; inv H5.
    * destruct b0; inv H3.
      ++ split. econstructor. split. reflexivity. constructor.
         intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
      ++ split. econstructor. split. reflexivity. constructor.
         intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
    * split. econstructor. split. reflexivity. constructor.
      intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
  - (*Pjmp_l*)
    unfold goto_label in H5. rewrite H in *.
    remember (label_pos l 0 (fn_code f)) as p; destruct p; inv H5.
    split.
    * econstructor. split. reflexivity. constructor.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
      eexists; econstructor; try eassumption; simpl; trivial.
      unfold goto_label. rewrite <- Heqp, H. reflexivity.
  - (*Pjcc*)
    remember (eval_testcond c rs) as p;destruct p; inv H5.
    destruct b0; inv H3.
    * unfold goto_label in H4. rewrite H in *.
      remember (label_pos l 0 (fn_code f)) as q; destruct q; inv H4.
      split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
         unfold goto_label. rewrite <- Heqq, H; reflexivity.
    * split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp; trivial.
  - (*Pjcc2*)
    remember (eval_testcond c1 rs) as p; destruct p; inv H5.
    destruct b0; inv H3.
    * remember (eval_testcond c2 rs) as q; destruct q; inv H4.
      destruct b0; inv H3.
      ++ unfold goto_label in H4. rewrite H in *.
         remember (label_pos l 0 (fn_code f)) as w; destruct w; inv H4.
         split.
         -- econstructor. split. reflexivity. constructor.
         -- intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
            eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
            unfold goto_label. rewrite <- Heqw, H; reflexivity.
      ++ split.
         -- econstructor. split. reflexivity. constructor.
         -- intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
            eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
    * remember (eval_testcond c2 rs) as q; destruct q; inv H4.
      split.
      ++ econstructor. split. reflexivity. constructor.
      ++ intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
         eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
  - (*Pjmptbl*)
    remember (rs r) as p; destruct p; inv H5.
    remember (list_nth_z tbl (Int.unsigned i)) as q; destruct q; inv H3.
    unfold goto_label in H4. rewrite H in *.
    remember (label_pos l 0 (fn_code f)) as w; destruct w; inv H4.
    split.
      * econstructor. split. reflexivity. constructor.
      * intros mm mm' EV'; inv EV'. destruct H2. inv H3. inv H2.
        eexists; econstructor; try eassumption; simpl; try rewrite <- Heqp, <- Heqq; trivial.
        unfold goto_label. rewrite <- Heqw, H; reflexivity.
  - (*Pmov_rm_a*)
    unfold exec_load in H5.
    remember (Mem.loadv Many32 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmov_mr_a*)
    unfold exec_store in H5.
    remember (Mem.storev Many32 m (eval_addrmode g a rs) (rs rs0)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pmovsd_fm_a*)
    unfold exec_load in H5.
    remember (Mem.loadv Many64 m (eval_addrmode g a rs)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate.
    destruct (Mem.load_loadbytes _ _ _ _ _ Heqp) as [bytes [LB V]]; simpl in LB.
    rewrite LB in H4; inv H4. inv H5.
    split.
    * constructor; simpl; trivial.
    * intros mm mm' EV'; inv EV'. inv H3.
      destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN].
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_load. rewrite <- Heqq; simpl; erewrite (Mem.loadbytes_load); trivial; eassumption.
      ++ rewrite <- Heqq, H2; reflexivity.
  - (*Pmovsd_mf_a*)
    unfold exec_store in H5.
    remember (Mem.storev Many64 m (eval_addrmode g a rs) (rs r1)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (eval_addrmode g a rs) as q.
    destruct q; try discriminate. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGN].
    apply Mem.store_storebytes in Heqp.
    split.
    * econstructor. split; simpl; trivial. eassumption.
    * intros mm mm' EV'; inv EV'. destruct H2. inv H3.
      eexists; econstructor; try eassumption; simpl.
      ++ unfold exec_store. rewrite <- Heqq; simpl. erewrite (Mem.storebytes_store); trivial.
      ++ rewrite <- Heqq; reflexivity.
  - (*Pallocframe*)
    remember (Mem.alloc m 0 sz) as a; symmetry in Heqa; destruct a as [m1 stk].
    remember (Mem.store Mint32 m1 stk
         (Int.unsigned (Int.add Int.zero ofs_link))
         (rs ESP)) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (Mem.store Mint32 m0 stk (Int.unsigned (Int.add Int.zero ofs_ra))
         (rs RA)) as q.
    destruct q; try discriminate; symmetry in Heqq. inv H5; inv H4.
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqp) as [_ ALIGNp].
    destruct (Mem.store_valid_access_3 _ _ _ _ _ _ Heqq) as [_ ALIGNq].
    apply Mem.store_storebytes in Heqp.
    apply Mem.store_storebytes in Heqq.
    rewrite Int.add_zero_l in *.
    split.
    * econstructor. split. eassumption.
      econstructor. split. eassumption.
      econstructor. split. eassumption.
      econstructor.
    * intros mm mm' EV'; inv EV'. destruct H2 as [ALLOC EV]. inv EV. inv H2. inv H4. destruct H2. inv H4.
      eexists; econstructor; try eassumption; simpl; repeat rewrite Int.add_zero_l; rewrite ALLOC;
      repeat erewrite Mem.storebytes_store; try eassumption; reflexivity.
  - (*Pfreeframe*)
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_ra))) as p.
    destruct p; try discriminate; symmetry in Heqp.
    remember (Mem.loadv Mint32 m (Val.add (rs ESP) (Vint ofs_link))) as q.
    destruct q; try discriminate; symmetry in Heqq.
    remember (rs ESP) as w; destruct w; try discriminate.
    remember (Mem.free m b0 0 sz) as t; destruct t; try discriminate.
    inv H5; inv H4.
    destruct (Mem.load_loadbytes _ _ _ _ _  Heqp) as [bytes1 [Bytes1 LD1]].
    destruct (Mem.load_loadbytes _ _ _ _ _  Heqq) as [bytes2 [Bytes2 LD2]].
    simpl in *; rewrite Bytes1, Bytes2 in *. inv H3.
    destruct (Mem.load_valid_access _ _ _ _ _ Heqp) as [_ ALIGN1].
    destruct (Mem.load_valid_access _ _ _ _ _ Heqq) as [_ ALIGN2].
    split.
    * econstructor; trivial. econstructor; trivial.  econstructor.
      split. simpl. rewrite <- Heqt; trivial. econstructor.
    * intros mm mm' EV'. inv EV'. inv H3. inv H5. destruct H3. inv H5. simpl in H3.
      remember (Mem.free mm b0 0 sz) as d; destruct d; try discriminate. inv H3.
      exploit (Mem.loadbytes_load Mint32). apply H2. assumption.
      exploit (Mem.loadbytes_load Mint32). apply H4. assumption.
      eexists; econstructor; try eassumption.
      ++ simpl. rewrite <- Heqw; simpl. rewrite H3, H5, <- Heqd. reflexivity.
      ++ simpl. rewrite <- Heqw; simpl. rewrite H3, H5, <- Heqd. rewrite H2, H4. reflexivity.
(* + (*builtin*)
  destruct ef; simpl in *; try solve [elim H4; trivial].
  - inv H7.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    split.
    * eapply ev_elim_app. eassumption.
      (*EFexternal helpers don't change memory - should follow from HFD*)
    * intros mm mm' MM. rewrite app_nil_r in MM.
      destruct (EVS _ _ MM); subst mm'.
      destruct (I64Helpers.is_I64_helperS_dec name sg). 2: elim H4; trivial.
      (*helpers don't access memory -- with stengthened HFD, proof will essesntially be like this:
      eexists. eapply asm_ev_step_builtin; try eassumption. simpl; trivial.
        eapply eval_builtin_args_ev_eval_builtin_args; eassumption.
        2: reflexivity.
        2: constructor; trivial. *)
  - inv H7.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    split.
    * eapply ev_elim_app. eassumption.
      (*EFbuiltin helpers don't change memory - should follow from HFD*)
    * intros mm mm' MM. rewrite app_nil_r in MM.
      destruct (EVS _ _ MM); subst mm'.
      destruct (is_I64_builtinS_dec name sg). 2: elim H4; trivial.
       (*helpers don't access memory -- with stengthened HFD, proof will essesntially be like this:
      eexists. eapply asm_ev_step_builtin; try eassumption. simpl; trivial.
        eapply eval_builtin_args_ev_eval_builtin_args; eassumption.
        2: reflexivity.
        2: constructor; trivial. *)
  - (*malloc*)
    inv H3; inv H7. rewrite H8 in ALLOC. inv ALLOC.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    apply Mem.store_storebytes in H9.
    split.
    * eapply ev_elim_app. eassumption.
      econstructor. split. eassumption.
      econstructor. split. eassumption. constructor.
    * intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [mm1 [EV1 EV2]].
      inv EV2. destruct H3. inv H5. destruct H7. inv H7.
      rename x into mm2. rename x0 into mm3.
      specialize (EVS _ _ EV1); destruct EVS; subst mm1.
      eexists. eapply asm_ev_step_builtin; try eassumption; simpl; trivial.
      ++ eapply eval_builtin_args_ev_eval_builtin_args; eassumption.
      ++ econstructor. eassumption. erewrite Mem.storebytes_store; try reflexivity; eassumption.
      ++ econstructor; try eassumption.
  - (*free*)
    inv H3; inv H7.
    destruct (Mem.load_loadbytes _ _ _ _ _ H8) as [bytes1 [LB1 SZ1]].
    rewrite LB1 in LB; inv LB. rewrite <- SZ1 in SZ; inv SZ.
    rewrite H10 in FR; inv FR.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    split.
    * eapply ev_elim_app. eassumption.
      econstructor. eassumption.
      econstructor. split. simpl. rewrite H10. reflexivity. constructor.
    * intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [mm1 [EV1 EV2]].
      inv EV2. inv H5. destruct H7. inv H7.
      rename x into mm2.
      specialize (EVS _ _ EV1); destruct EVS; subst mm1.
      simpl in H5.
      remember (Mem.free mm b0 (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz)) as d.
      destruct d; inv H5; symmetry in Heqd.
      eexists. eapply asm_ev_step_builtin; try eassumption; simpl; trivial.
      ++ eapply eval_builtin_args_ev_eval_builtin_args; eassumption.
      ++ econstructor; try eassumption.
         rewrite SZ1. apply Mem.loadbytes_load; assumption.
      ++ econstructor; eassumption.
  - (*memcpy*)
    inv H3; inv H7. rewrite LB in H14; inv H14. rewrite ST in H15; inv H15.
    destruct (eval_builtin_args_ev_elim_strong _ _ _ _ _ _ _ H6) as [EV EVS].
    split.
    * eapply ev_elim_app. eassumption.
      econstructor. eassumption.
      econstructor. split. eassumption. constructor.
    * intros mm mm' MM. apply ev_elim_split in MM; destruct MM as [mm1 [EV1 EV2]].
      inv EV2. inv H5. destruct H7. inv H7.
      rename x into mm2.
      specialize (EVS _ _ EV1); destruct EVS; subst mm1.
      eexists. eapply asm_ev_step_builtin; try eassumption; simpl; trivial.
      ++ eapply eval_builtin_args_ev_eval_builtin_args; eassumption.
      ++ econstructor; try eassumption.
      ++ econstructor; eassumption.*)
+ (*Step-to-external*)
  exploit extcall_arguments_ev_aux_elim_strong. apply H2. intros [EV HEV].
  split; trivial; intros.
  destruct (HEV _ _ H3); subst.
  eexists. eapply asm_ev_step_to_external; try eassumption. eapply extcall_arguments_ev_extcall_arguments. eassumption.
(*+ inv H1.
  destruct callee; simpl in *; try solve [contradiction].
  - inv H3. (*EFexternal helpers don't change memory - should follow from HFD*)
  - inv H3. (*EFbuiltin helpers don't change memory - should follow from HFD*)*)
+ (*loadframe*)
   destruct (store_args_ev_elim _ _ _ _ _ _ H1) as [TT [HTT EV]].
   unfold store_args_events in H2. rewrite H2 in HTT. inv HTT.
   split.
   * econstructor. split; eassumption.
   * intros mm mm' EV'. inv EV'. destruct H3.
     exploit store_args_rec_transfer. eassumption. eassumption. eassumption. intros SAR.
     eexists. econstructor; try eassumption.
Qed. (*due to extcall and builtins*)

Program Definition Asm_EvSem : @EvSem genv state.
Proof.
eapply Build_EvSem with (msem := Asm_mem_sem (*hf*)) (ev_step:=asm_ev_step).
+ intros. eapply asm_ev_ax1; try eassumption. (*helper_functions declared*)
+ eapply asm_ev_ax2; eassumption.
+ eapply asm_ev_fun; eassumption.
+ eapply asm_ev_elim_strong; eassumption.
Defined. (*helper_functions declared*)

End ASM_EV.
