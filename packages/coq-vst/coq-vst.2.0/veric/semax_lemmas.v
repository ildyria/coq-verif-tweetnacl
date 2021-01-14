Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.seplog.
Require Import VST.veric.assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.Clight_lemmas.

Local Open Scope pred.

Hint Resolve @now_later @andp_derives @sepcon_derives.

Lemma no_dups_swap:
  forall F V a b c, @no_dups F V (a++b) c -> @no_dups F V (b++a) c.
Proof.
unfold no_dups; intros.
rewrite map_app in *.
forget (map (@fst _ _) b) as bb.
forget (map (@fst _ _) a) as aa.
forget (map (var_name V) c) as cc.
clear - H.
destruct (list_norepet_append_inv _ _ _ H) as [? [? ?]].
apply list_norepet_append; auto.
apply list_norepet_append_commut; auto.
clear - H2.
unfold Coqlib.list_disjoint in *.
intros; apply H2; auto.
clear - H.
rewrite in_app in *.
intuition.
Qed.

Lemma join_sub_share_top: forall sh, join_sub Share.top sh -> sh = Share.top.
Proof.
intros.
generalize (top_correct' sh); intro.
apply join_sub_antisym; auto.
Qed.


Lemma opt2list2opt: forall {A:Type} (l: option A), list2opt (opt2list l) = l.
destruct l; auto.
Qed.


Lemma nat_of_Z_minus_le : forall z a b,
  b <= a ->
  (nat_of_Z (z - a) <= nat_of_Z (z - b))%nat.
Proof.
  intros.
  apply inj_le_rev.
  do 2 rewrite nat_of_Z_max.
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-a)).
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-b)).
  omega.
  omega.
  rewrite Coqlib.Zmax_spec.
  destruct (zlt 0 (z-b)); omega.
Qed.

Section SemaxContext.
Context (Espec: OracleKind).

Lemma universal_imp_unfold {A} {agA: ageable A}:
   forall B (P Q: B -> pred A) w,
     (ALL psi : B, P psi --> Q psi) w = (forall psi : B, (P psi --> Q psi) w).
Proof.
intros.
apply prop_ext; split; intros.
eapply H; eauto.
intro b; apply H.
Qed.

Lemma guard_environ_put_te':
 forall ge te ve Delta id v k,
 guard_environ Delta k (mkEnviron ge ve te)  ->
    (forall t : type * bool,
        (temp_types Delta) ! id = Some t -> tc_val (fst t) v) ->
 guard_environ (initialized id Delta) k (mkEnviron ge ve (Map.set id v te)).
Proof.
 intros.
 destruct H; split.
 apply typecheck_environ_put_te'; auto.
 destruct k; auto.
 destruct H1; split.
 apply H1.
 unfold initialized. destruct ((temp_types Delta) ! id); try destruct p; auto.
Qed.

Lemma prop_imp_derives {A}{agA: ageable A}:
  forall (P: Prop) (Q Q': pred A),  (P -> Q |-- Q') -> !!P --> Q |-- !!P --> Q'.
Proof.
 intros.
 repeat intro.
 apply H; auto.
Qed.

Lemma age_laterR {A} `{ageable A}: forall {x y}, age x y -> laterR x y.
Proof.
intros. constructor 1; auto.
Qed.
Hint Resolve @age_laterR.

(*
Lemma tycontext_sub_update_c:
 forall c (Delta Delta' : tycontext),
    tycontext_sub Delta Delta' -> tycontext_sub (update_tycon Delta c) (update_tycon Delta' c)
with tycontext_sub_update_l:
  forall l (Delta Delta' : tycontext),
    tycontext_sub Delta Delta' -> tycontext_sub (join_tycon_labeled l Delta) (join_tycon_labeled l Delta').
Proof.
clear tycontext_sub_update_c.
induction c; intros; simpl; auto.
apply initialized_sub; auto.
destruct o; auto.
apply initialized_sub; auto.
specialize (IHc1 _ _ H).
specialize (IHc2 _ _ H).
apply tycontext_sub_join; auto.
clear tycontext_sub_update_l.
induction l; simpl; intros; auto.
apply tycontext_sub_join; auto.
Qed.
*)

Lemma typecheck_environ_sub:
  forall Delta Delta', tycontext_sub Delta Delta' ->
   forall rho,
   typecheck_environ Delta' rho -> typecheck_environ Delta rho.
Proof.
intros ? ? [? [? [? [? Hs]]]] ?  [? [? [? ?]]].
split; [ | split; [ | split]].
* clear - H H3.
 hnf; intros.
 specialize (H id); rewrite H0 in H.
 destruct ((temp_types Delta') ! id) eqn:?H; try contradiction.
 destruct p. destruct H; subst.
 specialize (H3 id b0 t H1).
 destruct H3 as [v [? ?]].
 exists v; split; auto. destruct H3; [left | right]; auto.
 destruct b0; try contradiction.
 destruct (negb b); inv H2. apply I.
* clear - H0 H4.
  red in H4|-*.
 intros id ty. specialize (H4 id ty). rewrite <- H4.
 rewrite H0. clear; intuition.
* clear - H2 H5.
 hnf; intros. eapply H5.
 specialize (H2 id). hnf in H2. rewrite H in H2. eauto.
* clear - H6 H1 H2 H0.
 hnf; intros. specialize (H6 id t).
 specialize (H2 id); hnf in H2. rewrite H in H2.
 specialize (H6 H2).
 destruct H6; auto; right.
 destruct H3 as [t' ?]. exists t'.
 rewrite (H0 id); auto.
Qed.

Lemma semax'_post:
 forall {CS: compspecs} (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl rho,  !!(typecheck_environ (exit_tycon c Delta ek) rho ) && 
                proj_ret_assert R' ek vl rho 
         |-- proj_ret_assert R ek vl rho) ->
   semax' Espec Delta P c R' |-- semax' Espec Delta P c R.
Proof.
intros.
rewrite semax_fold_unfold.
apply allp_derives; intro psi.
apply allp_derives; intro Delta'.
apply prop_imp_derives; intros [TS HGG].
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply imp_derives; auto.
unfold rguard, guard.
apply andp_derives; auto.
apply allp_derives; intro ek.
apply allp_derives; intro vl.
apply allp_derives; intro te.
apply allp_derives; intro ve.
intros ? ?.
intros ? ? ? ? ?.
specialize (H0 _ H1 _ H2).
apply H0.
destruct H3 as [[? ?] ?].
split; auto.
split; auto.
specialize (H ek vl (construct_rho (filter_genv psi) ve te)).
destruct H3 as [H3 _].
rewrite prop_true_andp in H 
  by (eapply typecheck_environ_sub; eauto; apply exit_tycon_sub; auto).
forget (construct_rho (filter_genv psi) ve te) as rho.
clear - H H4.
destruct ek; simpl in *; intuition.
*
 destruct R; simpl in *; intuition.
 rewrite !prop_true_andp in H by auto.
 destruct R'; simpl in *; intuition.
 destruct H1 as [w1 [w2 [? [? ?]]]]; specialize (H w1); exists w1,w2; intuition.
*
 destruct R; simpl in *; intuition.
 rewrite !prop_true_andp in H by auto.
 destruct R'; simpl in *; intuition.
 destruct H1 as [w1 [w2 [? [? ?]]]]; specialize (H w1); exists w1,w2; intuition.
*
 destruct R; simpl in *; intuition.
 rewrite !prop_true_andp in H by auto.
 destruct R'; simpl in *; intuition.
 destruct H1 as [w1 [w2 [? [? ?]]]]; specialize (H w1); exists w1,w2; intuition.
*
 destruct R; simpl in *; intuition.
 destruct R'; simpl in *; intuition.
 destruct H4 as [w1 [w2 [? [? ?]]]]; specialize (H w1); exists w1,w2; intuition.
Qed.

Lemma semax'_pre:
 forall {CS: compspecs} P' Delta R P c,
  (forall rho, typecheck_environ Delta rho ->   P rho |-- P' rho)
   ->   semax' Espec Delta P' c R |-- semax' Espec Delta P c R.
Proof.
intros.
repeat rewrite semax_fold_unfold.
apply allp_derives; intro psi.
apply allp_derives; intro Delta'.
apply prop_imp_derives; intros [TS HGG].
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply imp_derives; auto.
unfold guard.
apply allp_derives; intro te.
apply allp_derives; intro ve.
intros ? ?.
intros ? ? ? ? ?.
eapply H0; eauto.
destruct H3 as [[? ?] ?].
split; auto.
split; auto.
eapply sepcon_derives; try apply H; auto.
destruct H3.
eapply typecheck_environ_sub; eauto.
Qed.

Lemma semax'_pre_post:
 forall
      {CS: compspecs} P' (R': ret_assert) Delta (R: ret_assert) P c,
   (forall rho, typecheck_environ Delta rho ->   P rho |-- P' rho) ->
   (forall ek vl rho, !!(typecheck_environ (exit_tycon c Delta ek) rho) 
                       &&  proj_ret_assert R ek vl rho 
                    |-- proj_ret_assert R' ek vl rho) ->
   semax' Espec Delta P' c R |-- semax' Espec Delta P c R'.
Proof.
intros.
eapply derives_trans.
apply semax'_pre; eauto.
apply semax'_post; auto.
Qed.

Lemma cl_corestep_fun': corestep_fun cl_core_sem.
Proof.  intro; intros. eapply cl_corestep_fun; eauto. Qed.
Hint Resolve cl_corestep_fun'.

Lemma derives_skip:
  forall {CS: compspecs} p Delta (R: ret_assert),
      (forall rho, p rho |-- proj_ret_assert R EK_normal None rho) ->
        semax Espec Delta p Clight.Sskip R.
Proof.
intros ? ? ? ?; intros.
intros n.
rewrite semax_fold_unfold.
intros psi Delta'.
apply prop_imp_i; intros [? HGG].
clear H0 Delta. rename Delta' into Delta.
intros ?w _ _. clear n.
intros k F.
intros ?w _ ?.
clear w. rename w0 into n.
intros te ve w ?.
destruct H0 as [H0' H0].
specialize (H0 EK_normal None te ve w H1).
simpl exit_cont in H0.
simpl in H0'. clear n H1. remember ((construct_rho (filter_genv psi) ve te)) as rho.
revert w H0.
apply imp_derives; auto.
apply andp_derives; auto.
apply andp_derives; auto.
repeat intro. (* simpl exit_tycon. *)
simpl.
specialize (H rho). destruct R; simpl in H. simpl tycontext.RA_normal.
rewrite sepcon_comm.
split; auto. rewrite prop_true_andp in H by auto.
eapply sepcon_derives; try apply H0; auto.

repeat intro.
specialize (H0 ora jm H1 H2).
destruct (@level rmap _ a).
constructor.
apply convergent_controls_safe with (State ve te k); auto.
simpl.

intros.
destruct H3 as [? [? ?]].
split3; auto.

econstructor; eauto.
Qed.

Lemma semax_extract_prop:
  forall {CS: compspecs} Delta (PP: Prop) P c Q,
           (PP -> semax Espec Delta P c Q) ->
           semax Espec Delta (fun rho => !!PP && P rho) c Q.
Proof.
intros.
intro w.
rewrite semax_fold_unfold.
intros gx Delta'.
apply prop_imp_i; intros [TS HGG].
intros w' ? ? k F w'' ? ?.
intros te ve w''' ? w4 ? [[[? ?] ?] ?].
rewrite sepcon_andp_prop in H8.
destruct H8.
specialize (H H8); clear PP H8.
hnf in H. rewrite semax_fold_unfold in H.
eapply H; try apply TS.
apply necR_refl.
split; auto.
apply TS. apply necR_refl.
eassumption.
eassumption.
eassumption.
eassumption.
eassumption.
split; auto.
split; auto.
split; auto.
Qed.

Lemma semax_extract_later_prop:
  forall {CS: compspecs} Delta (PP: Prop) P c Q,
           (PP -> semax Espec Delta (fun rho => (P rho)) c Q) ->
           semax Espec Delta (fun rho => (|> !!PP) && P rho) c Q.
Proof.
intros.
intro w.
rewrite semax_fold_unfold.
intros gx Delta'.
apply prop_imp_i; intros [TS HGG].
intros w' ? ? k F w'' ? ?.
intros te ve w''' ? w4 ? [[[? ?] ?] ?].

replace ((F (construct_rho (filter_genv gx) ve te) *
        (|>(!!PP) && (P (construct_rho (filter_genv gx) ve te))))%pred) with
        (|>!!PP && (F (construct_rho (filter_genv gx) ve te) *
         (P (construct_rho (filter_genv gx) ve te)))%pred) in H8.
Focus 2. {
  rewrite (sepcon_comm (F (construct_rho (filter_genv gx) ve te))
    (|>!!PP && P (construct_rho (filter_genv gx) ve te))).

 rewrite corable_andp_sepcon1 by (apply corable_later; apply corable_prop).

 rewrite sepcon_comm.
 reflexivity.
} Unfocus.
destruct H8.
simpl in H8.
destruct (age1 w4) eqn:?H.
+ assert (age w4 r) by auto.
  apply age_laterR in H12.
  specialize (H8 r H12).
  specialize (H H8); clear PP H8.
  hnf in H. rewrite semax_fold_unfold in H.
  eapply H. apply necR_refl. split; eassumption.
  apply necR_refl. eassumption. eassumption. eassumption.
  eassumption. eassumption.
  split; auto.
  split; auto.
  split; auto.
+ simpl.
  eapply af_level1 in H11; [| apply compcert_rmaps.R.ag_rmap].
  rewrite H11.
  constructor.
Qed.

Lemma semax_unfold {CS: compspecs}:
  semax Espec = fun Delta P c R =>
    forall (psi: Clight.genv) Delta' (w: nat)
          (TS: tycontext_sub Delta Delta')
          (HGG: genv_cenv psi = cenv_cs)
           (Prog_OK: believe Espec Delta' psi Delta' w) (k: cont) (F: assert),
        closed_wrt_modvars c F ->
       rguard Espec psi (exit_tycon c Delta') (frame_ret_assert R F) k w ->
       guard Espec psi Delta' (fun rho => F rho * P rho) (Kseq c :: k) w.
Proof.
unfold semax; rewrite semax_fold_unfold.
extensionality Delta P c R.
apply prop_ext; split; intros.
eapply (H w); eauto.
split; auto. split; auto.
intros psi Delta'.
apply prop_imp_i; intros [? HGG].
intros w' ? ? k F w'' ? [? ?].
eapply H; eauto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma semax_post' {CS: compspecs}:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl rho,  !!(typecheck_environ (exit_tycon c Delta ek) rho) 
                      &&  proj_ret_assert R' ek vl rho
                        |-- proj_ret_assert R ek vl rho) ->
   semax Espec Delta P c R' ->  semax Espec Delta P c R.
Proof.
unfold semax.
intros.
spec H0 n. revert n H0.
apply semax'_post.
auto.
Qed.

Lemma semax_post {CS: compspecs}:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall rho,  !!(typecheck_environ (update_tycon Delta c) rho) 
                      &&  RA_normal R' rho |-- RA_normal R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_break R' rho |-- RA_break R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_continue R' rho |-- RA_continue R rho) ->
   (forall vl rho, !! (typecheck_environ Delta rho) 
                      && RA_return R' vl rho |-- RA_return R vl rho) ->
   semax Espec Delta P c R' ->  semax Espec Delta P c R.
Proof.
unfold semax.
intros.
spec H3 n. revert n H3.
apply semax'_post.
intros; destruct ek; simpl;
repeat (apply normalize.derives_extract_prop; intro); rewrite ?prop_true_andp by auto;
specialize (H rho); specialize (H0 rho); specialize (H1 rho); specialize (H2 vl rho);
rewrite prop_true_andp in * by auto; auto.
Qed.

Lemma semax_pre {CS: compspecs}:
 forall P' Delta P c R,
   (forall rho,  !!(typecheck_environ Delta rho) &&  P rho |-- P' rho )%pred ->
     semax Espec Delta P' c R  -> semax Espec Delta P c R.
Proof.
unfold semax.
intros.
spec H0 n.
revert n H0.
apply semax'_pre.
repeat intro. apply (H rho a). split; auto.
Qed.

Lemma semax_pre_post {CS: compspecs}:
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
   (forall rho,  !!(typecheck_environ Delta rho) &&  P rho |-- P' rho )%pred ->
   (forall rho,  !!(typecheck_environ (update_tycon Delta c) rho) 
                      &&  RA_normal R' rho |-- RA_normal R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_break R' rho |-- RA_break R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_continue R' rho |-- RA_continue R rho) ->
   (forall vl rho, !! (typecheck_environ Delta rho) 
                      && RA_return R' vl rho |-- RA_return R vl rho) ->
   semax Espec Delta P' c R' ->  semax Espec Delta P c R.
Proof.
intros.
eapply semax_pre; eauto.
eapply semax_post; eauto.
Qed.

Lemma semax_skip {CS: compspecs}:
   forall Delta P, semax Espec Delta P Sskip (normal_ret_assert P).
Proof.
intros.
apply derives_skip.
intros.
simpl.
rewrite prop_true_andp by auto.
auto.
Qed.

Fixpoint list_drop (A: Type) (n: nat) (l: list A) {struct n} : list A :=
  match n with O => l | S i => match l with nil => nil | _ :: l' => list_drop A i l' end end.
Arguments list_drop [A] _ _.

Definition straightline (c: Clight.statement) :=
 forall ge ve te k m ve' te' k' m',
        cl_step ge (State ve te (Kseq c :: k)) m (State ve' te' k') m' ->  k=k'.

Lemma straightline_assign: forall e0 e, straightline (Clight.Sassign e0 e).
Proof.
unfold straightline; intros.
inv H; auto.
Qed.


Lemma extract_exists {CS: compspecs}:
  forall  (A : Type) (P : A -> assert) c Delta (R: A -> ret_assert),
  (forall x, semax Espec Delta (P x) c (R x)) ->
   semax Espec Delta (fun rho => exp (fun x => P x rho)) c (existential_ret_assert R).
Proof.
rewrite semax_unfold in *.
intros.
intros.
intros te ve ?w ? ?w ? ?.
rewrite exp_sepcon2 in H4.
destruct H4 as [[TC [x H5]] ?].
(*destruct H4 as [[[TC [x H5]] ?] ?].*)
specialize (H x).
specialize (H psi Delta' w TS HGG Prog_OK k F H0).
spec H. {
 clear - H1.
 unfold rguard in *.
 intros ek vl tx vx. specialize (H1 ek vl tx vx).
 red in H1.
 eapply subp_trans'; [| apply H1 ].
 apply derives_subp.
 apply andp_derives; auto.
 apply andp_derives; auto.
 clear.
 destruct (R x) eqn:?, ek; simpl;
 try (apply andp_derives; [auto | ]);
 (apply sepcon_derives; [ apply exp_right with x; rewrite Heqr; auto| auto]).
}
intros ? ? ?.
eapply H; eauto.
split; auto.
split; auto.
Qed.

Lemma extract_exists_pre {CS: compspecs}:
      forall
        (A : Type) (P : A -> assert) (c : Clight.statement)
         Delta (R : ret_assert),
       (forall x : A, semax Espec Delta (P x) c R) ->
       semax Espec Delta (fun rho => exp (fun x => P x rho)) c R.
Proof.
intros.
apply semax_post with (existential_ret_assert (fun _:A => R));
try (intros; apply normalize.derives_extract_prop; intro; apply exp_left; auto).
apply extract_exists; auto.
Qed.

Definition G0: funspecs := nil.

Definition empty_genv prog_pub cenv: Clight.genv :=
   Build_genv (Genv.globalenv (AST.mkprogram (F:=Clight.fundef)(V:=type) nil prog_pub (1%positive))) cenv.

Lemma empty_program_ok {CS: compspecs}: forall Delta ge w,
    glob_specs Delta = PTree.empty _ ->
    believe Espec Delta ge Delta w.
Proof.
intros Delta ge w ?.
intro b.
intros fsig cc A P Q.
intros ?n ? ?.
destruct H1 as [id [? [b0 [? ?]]]].
rewrite H in H1. rewrite PTree.gempty in H1.
inv H1.
Qed.

Definition all_assertions_computable  :=
  forall psi tx vx (Q: assert), exists k,  assert_safe Espec psi tx vx k = Q.
(* This is not generally true, but could be made true by adding an "assert" operator
  to the programming language
*)

Lemma ewand_TT_emp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}:
    ewand TT emp = emp.
Proof.
intros.
apply pred_ext; intros w ?.
destruct H as [w1 [w3 [? [? ?]]]].
hnf; eapply split_identity.
eapply join_comm; eauto.
auto.
exists w; exists w; split; auto.
change (identity w) in H.
rewrite identity_unit_equiv in H; auto.
Qed.

Lemma subp_derives' {A}{agA: ageable A}:
  forall P Q: pred A, (forall n, (P >=> Q) n) -> P |-- Q.
Proof.
intros.
intros n ?. eapply H; eauto.
Qed.

Lemma guard_environ_sub:
  forall {Delta Delta' f rho},
   tycontext_sub Delta Delta' ->
   guard_environ Delta' f rho ->
   guard_environ Delta f rho.
Proof.
intros.
destruct H0; split; auto.
eapply typecheck_environ_sub; eauto.
destruct f; auto.
destruct H1; split; auto.
destruct H as [? [? [? ?]]]. rewrite H4; auto.
Qed.

Lemma guard_environ_eqv:
  forall Delta Delta' f rho,
  tycontext_eqv Delta Delta' ->
  guard_environ Delta f rho -> guard_environ Delta' f rho.
Proof.
  intros.
  rewrite tycontext_eqv_spec in H.
  eapply guard_environ_sub; eauto.
  tauto.
Qed.

Lemma proj_frame_ret_assert:
 forall (R: ret_assert) (F: assert) ek vl,
  proj_ret_assert (frame_ret_assert R F) ek vl = 
  seplog.sepcon (proj_ret_assert R ek vl) F.
Proof.
intros; extensionality rho; destruct R, ek; simpl;
rewrite ?sepcon_andp_prop1; auto.
Qed.

Lemma semax_extensionality0 {CS: compspecs}:
       TT |--
      ALL Delta:tycontext, ALL Delta':tycontext,
      ALL P:assert, ALL P':assert,
      ALL c: statement, ALL R:ret_assert, ALL R':ret_assert,
       ((!! tycontext_sub Delta Delta'
       &&  (ALL ek: exitkind, ALL  vl : option val, ALL rho: environ,  
               (proj_ret_assert R ek vl rho >=> proj_ret_assert R' ek vl rho))
      && (ALL rho:environ, P' rho >=> P rho)  && semax' Espec Delta P c R) >=> semax' Espec Delta' P' c R').
Proof.
apply loeb.
intros w ? Delta Delta' P P' c R R'.
intros w1 ? w2 ? [[[? ?] ?] ?].
do 3 red in H2.
rewrite semax_fold_unfold; rewrite semax_fold_unfold in H5.
intros gx Delta''.
apply prop_imp_i; intros [TS HGG].
intros w3 ? ?.
specialize (H5 gx Delta'' _ (necR_refl _)
  (conj (tycontext_sub_trans _ _ _ H2 TS) HGG)
                  _ H6 H7).

intros k F w4 Hw4 [? ?].
specialize (H5 k F w4 Hw4).
assert ((rguard Espec gx (exit_tycon c Delta'') (frame_ret_assert R F) k) w4).
do 9 intro.
apply (H9 b b0 b1 b2 y H10 a' H11).
destruct H12; split; auto; clear H13.
pose proof I.
destruct H12; split; auto.
(* unfold frame_ret_assert in H14|-*. *)
rewrite proj_frame_ret_assert in H14|-*.
clear H12 H13.
revert a' H11 H14.
apply sepcon_subp' with (level w2).
apply H3.
auto.
apply necR_level in H6.
apply necR_level in Hw4.
eapply le_trans; try eassumption.
eapply le_trans; try eassumption.

specialize (H5 (conj H8 H10)). clear H8 H9 H10.
do 7 intro.
apply (H5 b b0 y H8 _ H9).
destruct H10; split; auto.
destruct H10; split; auto.
clear H10 H11.
revert a' H9 H12.
apply sepcon_subp' with (level w2); auto.
apply necR_level in H6.
apply necR_level in Hw4.
eapply le_trans; try eassumption.
eapply le_trans; try eassumption.
Qed.

Lemma semax_extensionality1 {CS: compspecs}:
  forall Delta Delta' (P P': assert) c (R R': ret_assert) ,
       tycontext_sub Delta Delta' ->
       ((ALL ek: exitkind, ALL  vl : option val, ALL rho: environ,  
          (proj_ret_assert R ek vl rho >=> proj_ret_assert R' ek vl rho))
      && (ALL rho:environ, P' rho >=> P rho)  && (semax' Espec Delta P c R) |-- semax' Espec Delta' P' c R').
Proof.
intros.
intros n ?.
apply (semax_extensionality0 n I Delta Delta' P P' c R R' _ (le_refl _) _ (necR_refl _)).
destruct H0;
split; auto.
destruct H0;
split; auto.
split; auto.
Qed.

Lemma semax_frame {CS: compspecs}:  forall Delta P s R F,
   closed_wrt_modvars s F ->
  semax Espec Delta P s R ->
    semax Espec Delta (fun rho => P rho * F rho) s (frame_ret_assert R F).
Proof.
intros until F. intros CL H.
rewrite semax_unfold.
rewrite semax_unfold in H.
intros.
pose (F0F := fun rho => F0 rho * F rho).
specialize (H psi Delta' w TS HGG Prog_OK k F0F).
spec H. {
 unfold F0F.
 clear - H0 CL.
 hnf in *; intros; simpl in *.
 rewrite <- CL. rewrite <- H0. auto.
 intuition.
 intuition.
}
replace (fun rho : environ => F0 rho * (P rho * F rho))
  with  (fun rho : environ => F0F rho * P rho).
*
apply H.
unfold F0F; clear - H1.
intros ek vl tx vx; specialize (H1 ek vl tx vx).
red in H1.
remember ((construct_rho (filter_genv psi) vx tx)) as rho.
red.
hnf; intros. specialize (H1 _ H).
hnf; intros. apply H1; auto.
destruct H2; split; auto. destruct H2; split; auto.
rewrite proj_frame_ret_assert in H4|-*.
rewrite proj_frame_ret_assert.
rewrite seplog.sepcon_assoc.
eapply sepcon_derives; try apply H4; auto. simpl.
rewrite sepcon_comm; auto.
*
unfold F0F.
extensionality rho.
rewrite sepcon_assoc.
f_equal. apply sepcon_comm.
Qed.

Lemma assert_safe_last:
  forall ge ve te st rho w,
   (forall w', age w w' -> assert_safe Espec ge ve te st rho w) ->
    assert_safe Espec ge ve te st rho w.
Proof.
intros.
case_eq (age1 w). auto.
clear H.
repeat intro.
rewrite (af_level1 age_facts) in H.
rewrite H. simpl.
constructor.
Qed.

Lemma pred_sub_later' {A} `{H: ageable A}:
  forall (P Q: pred A),
           (|> P >=> |> Q)  |--  (|> (P >=> Q)).
Proof.
intros.
rewrite later_fash; auto.
rewrite later_imp.
auto.
Qed.

Lemma later_strengthen_safe1:
  forall (P: pred rmap) ge ve te k rho,
              ((|> P) >=> assert_safe Espec ge ve te k rho) |--   |>  (P >=> assert_safe Espec ge ve te k rho).
Proof.
intros.
intros w ?.
apply (@pred_sub_later' _ _ P  (assert_safe Espec ge ve te k rho)); auto.
eapply subp_trans'; try apply H.
apply derives_subp; clear.
intros w0 ?.
intros w' ?.
simpl in H0.
revert H; induction H0; intros.
simpl in *; intros.
subst y. change (level (m_phi jm)) with (level jm).
generalize (oracle_unage _ _ H); intros [jm0 [? ?]]. subst x.
eapply age_safe; try eassumption.
specialize (H0 ora jm0 H1 (eq_refl _)).
apply H0.
apply IHclos_trans2.
eapply pred_nec_hereditary; eauto.
Qed.

End SemaxContext.

Hint Resolve @age_laterR.


Fixpoint filter_seq (k: cont) : cont :=
 match k with
  | Kseq s :: k1 => filter_seq k1
  | _ => k
  end.

Lemma cons_app: forall A (x: A) (y: list A), x::y = (x::nil)++y.
Proof. auto. Qed.

Lemma cons_app': forall A (x:A) y z,
      x::y++z = (x::y)++z.
Proof. auto. Qed.

Lemma cat_prefix_empty:
   forall {A} prefix (ctl: list A), ctl =  prefix ++ ctl -> prefix = nil.
Proof.
do 3 intro.
destruct prefix; auto; intro; elimtype False.
assert (length ctl = length ((a::prefix) ++ ctl)).
f_equal; auto.
simpl in H0.
rewrite app_length in H0.
omega.
Qed.

Definition true_expr : Clight.expr := Clight.Econst_int Int.one (Tint I32 Signed noattr).


(* BEGIN Lemmas duplicated from Clight_sim. v *)
Lemma dec_skip: forall s, {s=Sskip}+{s<>Sskip}.
Proof.
 destruct s; try (left; congruence); right; congruence.
Qed.

Lemma strip_step:  (* This one uses equality, one in Clight_sim uses <->  *)
  forall ge ve te k m st' m',
     cl_step ge (State ve te (strip_skip k)) m st' m' =
    cl_step ge (State ve te k) m st' m'.
Proof.
intros.
 apply prop_ext.
 induction k; intros; split; simpl; intros; try destruct IHk; auto.
 destruct a; try destruct s; auto.
  constructor; auto.
 destruct a; try destruct s; auto.
 inv H. auto.
Qed.
(* END lemmas duplicated *)

 Lemma strip_skip_app:
  forall k k', strip_skip k = nil -> strip_skip (k++k') = strip_skip k'.
Proof. induction k; intros; auto. destruct a; inv H. destruct s; inv H1; auto.
  simpl. apply IHk. auto.
Qed.

Lemma strip_strip: forall k, strip_skip (strip_skip k) = strip_skip k.
Proof.
induction k; simpl.
auto.
destruct a; simpl; auto.
destruct (dec_skip s).
subst; auto.
destruct s; auto.
Qed.

Lemma strip_skip_app_cons:
 forall {k c l}, strip_skip k = c::l -> forall k', strip_skip  (k++k') = c::l++k'.
Proof. intros. revert k H;  induction k; intros. inv H.
  destruct a; try solve [simpl in *; auto];
  try solve [simpl in *; rewrite cons_app'; rewrite H; auto].
 destruct (dec_skip s). subst. simpl in *; auto.
 destruct s; inv H; simpl; auto.
Qed.


Lemma filter_seq_current_function:
  forall ctl1 ctl2, filter_seq ctl1 = filter_seq ctl2 ->
       current_function ctl1 = current_function ctl2.
Proof.
  intros ? ? H0. revert ctl2 H0; induction ctl1; simpl; intros.
  revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
  destruct a; auto; revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
Qed.

Lemma filter_seq_call_cont:
  forall ctl1 ctl2, filter_seq ctl1 = filter_seq ctl2 -> call_cont ctl1 = call_cont ctl2.
Proof.
  intros ? ? H0. revert ctl2 H0; induction ctl1; simpl; intros.
  revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
  destruct a; auto; revert H0; induction ctl2; simpl; intros; try destruct a; try congruence; auto.
Qed.

Lemma call_cont_app_nil:
  forall l k, call_cont l = nil -> call_cont (l++k) = call_cont k.
Proof.
 intros l k; revert k; induction l; simpl; intros;
   try destruct a; simpl in *; try congruence; auto.
Qed.
Lemma call_cont_app_cons:
  forall l c l', call_cont l = c::l' -> forall k, call_cont (l++k) = c::l' ++ k.
Proof.
  intros; revert c l' k H; induction l; simpl; intros;
   try destruct a; simpl in *; try congruence; auto.
Qed.

Lemma and_FF : forall {A} `{ageable A} (P:pred A),
  P && FF = FF.
Proof.
  intros. rewrite andp_comm. apply FF_and.
Qed.

Lemma sepcon_FF : forall {A}{JA: Join A}{PA: Perm_alg A}{AG: ageable A}{XA: Age_alg A} (P:pred A),
  (P * FF = FF)%pred.
Proof.
  intros. rewrite sepcon_comm. apply FF_sepcon.
Qed.

Section extensions.

Context (Espec : OracleKind).

Lemma age1_resource_decay:
  forall jm jm', age jm jm' -> resource_decay (nextblock (m_dry jm)) (m_phi jm) (m_phi jm').
Proof.
 intros. split.
 apply age_level in H.
 change (level (m_phi jm)) with (level jm).
 change (level (m_phi jm')) with (level jm').
 omega.
 intro l. split. apply juicy_mem_alloc_cohere. left.
 symmetry; apply age1_resource_at with (m_phi jm); eauto.
  destruct (age1_juicy_mem_unpack _ _ H); auto.
 symmetry; apply resource_at_approx.
Qed.

Lemma safe_loop_skip:
  forall
    ge ora ve te k m,
    jsafeN (@OK_spec Espec) ge (level m) ora
           (State ve te (Kseq (Sloop Clight.Sskip Clight.Sskip) :: k)) m.
Proof.
  intros.
  remember (level m)%nat as N.
  destruct N; [constructor|].
  case_eq (age1 m); [intros m' ? |  intro; apply age1_level0 in H; omegaContradiction].
  apply safeN_step with
    (c' := State ve te (Kseq Sskip :: Kseq Scontinue :: Kloop1 Sskip Sskip :: k))
    (m'0 := m').
  split3.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  repeat econstructor.
  apply age1_resource_decay; auto. apply age_level; auto.
  assert (N = level m')%nat.
  apply age_level in H; omega.
  clear HeqN m H. rename m' into m.
  revert m H0; induction N; intros; simpl; [constructor|].
  case_eq (age1 m); [intros m' ? |  intro; apply age1_level0 in H; omegaContradiction].
  apply safeN_step
    with (c' := State ve te (Kseq Sskip :: Kseq Scontinue :: Kloop1 Sskip Sskip :: k))
         (m'0 := m').
  split3.
  replace (m_dry m') with (m_dry m) by (destruct (age1_juicy_mem_unpack _ _ H); auto).
  repeat constructor.
 apply age1_resource_decay; auto. apply age_level; auto.
  eapply IHN; eauto.
  apply age_level in H. omega.
Qed.

Lemma safe_seq_skip ge n ora ve te k m :
  jsafeN OK_spec ge n ora (State ve te k) m ->
  jsafeN OK_spec ge n ora (State ve te (Kseq Sskip :: k)) m.
Proof.
inversion 1; subst. constructor.
econstructor; eauto. simpl. destruct H0 as (?&?&?). split3; eauto.
eapply step_skip; eauto.
simpl in *; congruence.
simpl in *. unfold cl_halted in H0. congruence.
Qed.

Lemma safe_seq_skip' ge n ora ve te k m :
  jsafeN OK_spec ge n ora (State ve te (Kseq Sskip :: k)) m ->
  jsafeN OK_spec ge n ora (State ve te k) m.
Proof.
inversion 1; subst. constructor.
econstructor; eauto. simpl. destruct H0 as (?&?&?). split3; eauto.
inv H0; auto.
simpl in *; congruence.
simpl in *. unfold cl_halted in H0. congruence.
Qed.

Lemma safe_step_forward:
  forall psi n ora st m,
   cl_at_external st = None ->
   j_halted cl_core_sem st  = None ->
   jsafeN (@OK_spec Espec) psi (S n) ora st m ->
 exists st', exists m',
   jstep cl_core_sem psi st m st' m' /\
   jsafeN (@OK_spec Espec) psi n ora  st' m'.
Proof.
 intros.
 inv H1.
 eexists; eexists; split; eauto.
 solve[destruct H3 as (?&?&?); split3; eauto].
 simpl in H3; rewrite H3 in H; congruence.
 simpl in H2; unfold cl_halted in H2. congruence.
Qed.

Lemma safeN_strip:
  forall ge n ora ve te k m,
     jsafeN (@OK_spec Espec) ge n ora (State ve te (strip_skip k)) m =
     jsafeN (@OK_spec Espec) ge n ora (State ve te k) m.
Proof.
 intros.
 destruct n. apply prop_ext; simpl; intuition.
 constructor. constructor.
 apply prop_ext; split; intros H.
 { induction k. simpl in H. auto. destruct a; auto.
   destruct (dec_skip s); subst.
   simpl in H|-*. apply IHk in H. apply safe_seq_skip; auto.
   destruct s; simpl in *; congruence. }
 { induction k. simpl. auto. destruct a; auto.
   destruct (dec_skip s); subst.
   simpl in *. apply IHk. apply safe_seq_skip'; auto.
   destruct s; simpl in *; congruence. }
Qed.

Local Open Scope nat_scope.

Definition control_as_safe ge n ctl1 ctl2 :=
 forall (ora : OK_ty) (ve : env) (te : temp_env) (m : juicy_mem) (n' : nat),
     n' <= n ->
     jsafeN (@OK_spec Espec) ge n' ora (State ve te ctl1) m ->
     jsafeN (@OK_spec Espec) ge n' ora (State ve te ctl2) m.

Fixpoint prebreak_cont (k: cont) : cont :=
  match k with
  | Kloop1 s e3 :: k' => k
  | Kseq s :: k' => prebreak_cont k'
  | Kloop2 s e3 :: _ => nil  (* stuck *)
  | Kswitch :: k' => k
  | _ =>  nil (* stuck *)
  end.

Lemma prebreak_cont_is: forall k,
  match (prebreak_cont k) with
  | Kloop1 _ _ :: _ => True
  | Kswitch :: _ => True
  | nil => True
  | _ => False
  end.
Proof.
induction k; simpl; auto.
destruct (prebreak_cont k); try contradiction; destruct a; auto.
Qed.

Lemma find_label_prefix:
  forall lbl s ctl k, find_label lbl s ctl = Some k -> exists j, k = j++ctl
with
  find_label_ls_prefix:
  forall lbl s ctl k, find_label_ls lbl s ctl = Some k -> exists j, k = j++ctl.
Proof.
 intros.
  clear find_label_prefix.
  revert ctl k H; induction s; simpl; intros; try congruence.
  revert H; case_eq (find_label lbl s1 (Kseq s2 :: ctl)); intros; [inv H0 | auto ].
  destruct (IHs1 _ _ H) as [j ?]. exists (j++ (Kseq s2::nil)); rewrite app_ass; auto.
  revert H; case_eq (find_label lbl s1 ctl); intros; [inv H0 | auto ]; auto.
  revert H; case_eq (find_label lbl s1 (Kseq Scontinue :: Kloop1 s1 s2 :: ctl)); intros; [inv H0 | auto ].
  destruct (IHs1 _ _ H) as [j ?]. exists (j++ (Kseq Scontinue :: Kloop1 s1 s2::nil)); rewrite app_ass; auto.
  destruct (IHs2 _ _ H0) as [j ?]. exists (j++ (Kloop2 s1 s2::nil)); rewrite app_ass; auto.
  destruct (find_label_ls_prefix _ _ _ _ H) as [j ?]. exists (j++(Kswitch :: nil)); rewrite app_ass; auto.
  if_tac in H. subst l. inv H.
  exists (Kseq s :: nil); auto.
  apply IHs; auto.

 induction s; simpl; intros. inv H.
 revert H; case_eq (find_label lbl s (Kseq (seq_of_labeled_statement s0) :: ctl)); intros.
 inv H0.
 destruct (find_label_prefix _ _ _ _ H) as [j ?]; exists (j++Kseq (seq_of_labeled_statement s0) ::nil); rewrite app_ass; auto.
 auto.
Qed.


Lemma find_label_None:
  forall lbl s ctl, find_label lbl s ctl = None -> forall ctl', find_label lbl s ctl' = None
with
  find_label_ls_None:
  forall lbl s ctl, find_label_ls lbl s ctl = None ->  forall ctl', find_label_ls lbl s ctl' = None.
Proof.
clear find_label_None; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 try (rewrite (IHs1 _ H); eauto).
 eauto.
 destruct (ident_eq lbl l). inv H. eapply IHs; eauto.

clear find_label_ls_None; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 try (rewrite (IHs1 _ H); eauto).
 eauto.
 rewrite (find_label_None _ _ _ H). eauto.
Qed.

Lemma find_label_prefix2':
 forall lbl s k1 pre, find_label lbl s k1 = Some (pre++k1) ->
               forall k2, find_label lbl s k2 = Some (pre++k2)
with find_label_ls_prefix2':
 forall lbl s k1 pre, find_label_ls lbl s k1 = Some (pre++k1) ->
               forall k2, find_label_ls lbl s k2 = Some (pre++k2) .
Proof.
intros. clear find_label_prefix2'.
revert pre k1 H k2; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 try
 (destruct (find_label_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre;
  erewrite app_ass in H; simpl in H;
  rewrite (IHs1 _ _ H); rewrite app_ass; reflexivity);
 try solve [erewrite (find_label_None); eauto].
 rewrite (IHs1 _ _ H); auto.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k1) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k1)
   in H.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k2) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k2).
destruct (find_label_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre.
  erewrite app_ass in H; simpl in H;
  rewrite (IHs1 _ _ H); rewrite app_ass; reflexivity.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k1) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k1)
   in H.
 change (Kseq Scontinue :: Kloop1 s1 s2 :: k2) with ((Kseq Scontinue :: Kloop1 s1 s2 :: nil) ++ k2).
 erewrite (find_label_None); eauto.
 destruct (find_label_prefix _ _ _ _ H0) as [j Hj];
  rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre.
  erewrite app_ass in H0; simpl in H0;
  rewrite (IHs2 _ _ H0); rewrite app_ass; reflexivity.
destruct (find_label_ls_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre.
  erewrite app_ass in H; simpl in H.
  rewrite (find_label_ls_prefix2' _ _ _ _ H); rewrite app_ass; reflexivity.
  if_tac. inv H. rewrite cons_app in H2. apply app_inv_tail in H2; subst. reflexivity.
  eauto.

intros. clear find_label_ls_prefix2'.
revert pre k1 H k2; induction s; simpl; intros; try congruence;
 try match type of H with match ?A with Some _ => _| None => _ end = _
                => revert H; case_eq A; intros; [inv H0 | ]
       end;
 eauto.
 (destruct (find_label_prefix _ _ _ _ H) as [j Hj];
 rewrite cons_app in Hj; rewrite <- app_ass in Hj; apply app_inv_tail in Hj; subst pre;
  erewrite app_ass in H; simpl in H).
  rewrite (find_label_prefix2' _ _ _ _ H); rewrite app_ass; reflexivity;
 try solve [erewrite (find_label_ls_None); eauto].
  erewrite (find_label_None); eauto.
Qed.

Lemma find_label_prefix2:
  forall lbl s pre j ctl1 ctl2,
   find_label lbl s (pre++ctl1) = Some (j++ctl1) ->
   find_label lbl s (pre++ctl2) = Some (j++ctl2).
Proof.
intros.
 destruct (find_label_prefix _ _ _ _ H).
 rewrite <- app_ass in H0.
 apply  app_inv_tail in H0. subst j.
 rewrite app_ass in *.
 forget (pre++ctl1) as k1. forget (pre++ctl2) as k2.
 clear - H. rename x into pre.
 eapply find_label_prefix2'; eauto.
Qed.

Lemma corestep_preservation_lemma:
   forall ge ctl1 ctl2 ora ve te m n c l c' m',
       filter_seq ctl1 = filter_seq ctl2 ->
      (forall k : list cont', control_as_safe ge n (k ++ ctl1) (k ++ ctl2)) ->
      control_as_safe ge (S n) ctl1 ctl2 ->
      jstep cl_core_sem ge (State ve te (c :: l ++ ctl1)) m c' m' ->
      jsafeN (@OK_spec Espec) ge n ora c' m' ->
   exists c2 : corestate,
     exists m2 : juicy_mem,
       jstep cl_core_sem ge (State ve te (c :: l ++ ctl2)) m c2 m2 /\
       jsafeN (@OK_spec Espec) ge n ora c2 m2.
Proof. intros until m'. intros H0 H4 CS0 H H1.
  remember (State ve te (c :: l ++ ctl1)) as q. rename c' into q'.
  destruct H as [H [Hb Hc]].
  remember (m_dry m) as dm; remember (m_dry m') as dm'.
  revert c l m Heqdm m' Heqdm' Hb Hc H1 Heqq; induction H; intros; try inv Heqq.
  (* assign *)
  do 2 eexists; split; [split3; [econstructor; eauto | auto | auto ] | apply H4; auto ].
  (* set *)
  do 2 eexists; split; [split3; [ | eassumption | auto ] | ].
  rewrite <- Heqdm'; econstructor; eauto.
  apply H4; auto.
  (* call_internal *)
  do 2 eexists; split; [split3; [econstructor; eauto | auto | auto ] |  ].
  do 3 rewrite cons_app'. apply H4; auto.
  (* call_external *)
{ do 2 eexists; split; [split3; [ | eassumption | auto ] | ].
  rewrite <- Heqdm';  eapply step_call_external; eauto.
  destruct n; [constructor|].
  inv H5.
  { destruct H7 as (?&?&?). inv H5. }
  { eapply safeN_external; eauto.
    intros ret m'0 z'' n'' Hargsty Hretty Hle H10 H11; specialize (H9 ret m'0 z'' n'' Hargsty Hretty Hle H10 H11).
    destruct H9 as [c' [? ?]]. simpl in H5. unfold cl_after_external in *.
    destruct ret as [ret|]. destruct optid.
    exists (State ve (PTree.set i ret te) (l ++ ctl2)); split; auto.
    inv H5. apply H4; auto.
    destruct H10 as (?&?&?). inv H5.
    exists (State ve te (l ++ ctl2)); split; auto. apply H4; auto.
    destruct optid; auto.
    exists (State ve (PTree.set i Vundef te) (l ++ ctl2)); split; auto.  inv H5. apply H4; auto.
    exists (State ve te (l ++ ctl2)); split; auto. apply H4; auto.
    inv H5. auto. }
  { simpl in H6. unfold cl_halted in H6. congruence. } }
  (* sequence  *)
  { destruct (IHcl_step (Kseq s1) (Kseq s2 :: l)
            _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _))
      as [c2 [m2 [? ?]]]; clear IHcl_step.
    destruct H2 as [H2 [H2b H2c]].
    exists c2, m2; split; auto. split3; auto. constructor. apply H2. }
  (* skip *)
  { destruct l.
    simpl in H.
   assert (jsafeN (@OK_spec Espec) ge (S n) ora (State ve te ctl1) m0).
   eapply safe_corestep_backward; eauto; split3; eauto.
   apply CS0 in H2; auto.
    eapply safe_step_forward in H2; auto.
   destruct H2 as [st2 [m2 [? ?]]]; exists st2; exists m2; split; auto.
   simpl.
     destruct H2 as [H2 [H2b H2c]].
    split3; auto.
    rewrite <- strip_step. simpl. rewrite strip_step; auto.
    destruct (IHcl_step c l _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _))
      as [c2 [m2 [? ?]]]; clear IHcl_step.
    exists c2; exists m2; split; auto.
    destruct H2 as [H2 [H2b H2c]].
   simpl.
   split3; auto.
   rewrite <- strip_step.
   change (strip_skip (Kseq Sskip :: c :: l ++ ctl2)) with (strip_skip (c::l++ctl2)).
   rewrite strip_step; auto. }
  (* continue *)
  case_eq (continue_cont l); intros.
  assert (continue_cont (l++ctl1) = continue_cont (l++ctl2)).
  clear - H0 H2.
  induction l; simpl in *.
 revert ctl2 H0; induction ctl1; simpl; intros.
 revert H0; induction ctl2; simpl; intros; auto.
 destruct a; simpl in *; auto. inv H0. inv H0.
 destruct a; auto.
 revert H0; induction ctl2; simpl; intros. inv H0.
 destruct a; try congruence. rewrite <- (IHctl2 H0).
 f_equal.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence.
 auto.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence.
 auto.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence.
 auto.
 destruct a; try congruence. auto. auto.
  rewrite H3 in H.
  exists st', m'0; split; auto.
  split3; auto.
  constructor. auto.
  assert (forall k, continue_cont (l++k) = c::l0++k).
  clear - H2. revert H2; induction l; intros; try destruct a; simpl in *; auto; try discriminate.
  repeat rewrite cons_app'. f_equal; auto.
  rewrite H3 in H, IHcl_step.
  destruct (IHcl_step _ _ _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2,m2; split; auto.
   destruct H5 as [H5 [H5b H5c]].
 split3; auto.
 constructor. rewrite H3; auto.
  (* break *)
Focus 1.
  case_eq (prebreak_cont l); intros.
  assert (break_cont (l++ctl1) = break_cont (l++ctl2)).
  clear - H0 H2.
  revert H2; induction l; simpl; intros; try destruct a; try congruence.
  revert ctl2 H0; induction ctl1; simpl; intros.
 revert H0; induction ctl2; simpl; intros; try destruct a; try congruence. auto.
 destruct a. auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 revert H0; induction ctl2; try destruct a; simpl; intros; try congruence; auto.
 destruct s; auto.
  rewrite H3 in H.
  exists st', m'0; split; auto.
  split3; auto.
  constructor. auto.
  assert (PB:= prebreak_cont_is l); rewrite H2 in PB.
  destruct c; try contradiction.
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (semantics.corestep (juicy_core_sem cl_core_sem) ge (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (safe_corestep_backward (juicy_core_sem cl_core_sem) OK_spec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  assert (forall k, break_cont (l++k) = l0++k).
  clear - H2.
  revert H2; induction l; intros; try destruct a; simpl in *; auto; congruence.
  rewrite H3 in H.
  destruct l0; simpl in *.
  hnf in CS0.
  specialize (CS0 ora ve te m0 (S n)).
  assert (semantics.corestep (juicy_core_sem cl_core_sem) ge (State ve te ctl1) m0 st' m'0).
  split3; auto.
  pose proof (safe_corestep_backward (juicy_core_sem cl_core_sem) OK_spec ge _ _ _ _ _ _ H5 H1).
  apply CS0 in H6; auto.
  destruct (safe_step_forward ge n ora (State ve te ctl2) m0) as [c2 [m2 [? ?]]]; auto.
  exists c2; exists m2; split; auto.
  destruct H7;  constructor; auto. constructor; auto. rewrite H3. auto.
  destruct (IHcl_step c l0 m0 (eq_refl _) m'0 (eq_refl _)) as [c2 [m2 [? ?]]]; auto.
  rewrite H3; auto.
  exists c2,m2; split; auto.
  destruct H5; split; auto. constructor; auto. rewrite H3; auto.
  (* ifthenelse *)
  exists (State ve te (Kseq (if b then s1 else s2) :: l ++ ctl2)), m'.
  split. split3; auto. rewrite <- Heqdm'. econstructor; eauto.
  rewrite cons_app. rewrite <- app_ass.
  apply H4; auto.
  (* loop *)
  change (Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: l ++ ctl1) with
               ((Kseq s1 :: Kseq Scontinue :: Kloop1 s1 s2 :: l) ++ ctl1) in H1.
  eapply H4 in H1.
  do 2 eexists; split; eauto.
   split3; auto. rewrite <- Heqdm'.
  econstructor; eauto. omega.
  (* loop2 *)
  change (Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: l ++ ctl1) with
              ((Kseq s :: Kseq Scontinue :: Kloop1 s a3 :: l) ++ ctl1) in H1.
  apply H4 in H1; auto.
  do 2 eexists; split; eauto.   split3; auto. rewrite <- Heqdm'.  econstructor; eauto.
 (* return *)
  case_eq (call_cont l); intros.
  rewrite call_cont_app_nil in * by auto.
  exists (State ve' te'' k'), m'0; split; auto.
  split3; auto.
  econstructor; try eassumption. rewrite call_cont_app_nil; auto.
  rewrite <- (filter_seq_call_cont _ _ H0); auto.
  rewrite (call_cont_app_cons _ _ _ H6) in H. inv H.
  do 2 eexists; split.
  split3; eauto.
  econstructor; try eassumption.
 rewrite (call_cont_app_cons _ _ _ H6). reflexivity.
  apply H4; auto.
 (* switch *)
  do 2 eexists; split; [split3; [| eauto | eauto] | ].
  rewrite <- Heqdm'. econstructor; eauto.
  do 2 rewrite cons_app'. apply H4; auto.
 (* label *)
  destruct (IHcl_step _ _  _ (eq_refl _) _ (eq_refl _) Hb Hc H1 (eq_refl _)) as [c2 [m2 [? ?]]]; clear IHcl_step.
  exists c2, m2; split; auto.
   destruct H2 as [H2 [H2b H2c]].
  split3; auto.
  constructor; auto.
 (* goto *)
  case_eq (call_cont l); intros.
  do 2 eexists; split; [ | apply H1].
  split3; auto.
  rewrite <- Heqdm'; econstructor. 2: rewrite call_cont_app_nil; auto.
  instantiate (1:=f).
  generalize (filter_seq_current_function ctl1 ctl2 H0); intro.
  clear - H3 H2 CUR.
  revert l H3 H2 CUR; induction l; simpl; try destruct a; intros; auto; try congruence.
  rewrite call_cont_app_nil in H by auto.
  rewrite <- (filter_seq_call_cont ctl1 ctl2 H0); auto.
  rewrite (call_cont_app_cons _ _ _ H2) in H.
  assert (exists j, k' = j ++ ctl1).
  clear - H2 H.
  assert (exists id, exists f, exists ve, exists te, c =  Kcall id f ve te).
  clear - H2; induction l; [inv H2 | ].
  destruct a; simpl in H2; auto. inv H2; do 4 eexists; reflexivity.
  destruct H0 as [id [ff [ve [te ?]]]]. clear H2; subst c.
  change (find_label lbl (fn_body f)
      ((Kseq (Sreturn None) :: Kcall id ff ve te :: l0) ++ ctl1) = Some k') in H.
  forget (Kseq (Sreturn None) :: Kcall id ff ve te :: l0) as pre.
  assert (exists j, k' = j++ (pre++ctl1));
   [ | destruct H0 as [j H0]; exists (j++pre); rewrite app_ass; auto ].
  forget (pre++ctl1) as ctl. forget (fn_body f) as s;  clear - H.
 eapply find_label_prefix; eauto.
  destruct H3 as [j ?].
  subst k'.
  exists (State ve te (j++ctl2)), m'; split; [ | apply H4; auto].
  split3; auto.
  rewrite <- Heqdm'; econstructor.
  instantiate (1:=f).
  clear - CUR H2.
  revert f c l0 CUR H2; induction l; simpl; intros. inv H2.
  destruct a; simpl in *; eauto.
  rewrite (call_cont_app_cons _ _ _ H2).
  clear - H2 H.
  change (Kseq (Sreturn None) :: c :: l0 ++ ctl1) with ((Kseq (Sreturn None) :: c :: l0) ++ ctl1) in H.
  change (Kseq (Sreturn None) :: c :: l0 ++ ctl2) with ((Kseq (Sreturn None) :: c :: l0) ++ ctl2).
  forget (Kseq (Sreturn None) :: c :: l0)  as pre.
clear - H.
 eapply find_label_prefix2; eauto.
Qed.

Lemma control_as_safe_le:
  forall n' n ge ctl1 ctl2, n' <= n -> control_as_safe ge n ctl1 ctl2 -> control_as_safe ge n' ctl1 ctl2.
Proof.
 intros. intro; intros. eapply H0; auto; omega.
Qed.

Lemma control_suffix_safe :
    forall
      ge n ctl1 ctl2 k,
      filter_seq ctl1 = filter_seq ctl2 ->
      control_as_safe ge n ctl1 ctl2 ->
      control_as_safe ge n (k ++ ctl1) (k ++ ctl2).
  Proof.
    intro ge. induction n using (well_founded_induction lt_wf).
    intros. hnf; intros.
    destruct n'; [ constructor | ].
    assert (forall k, control_as_safe ge n' (k ++ ctl1) (k ++ ctl2)).
    intro; apply H; auto. apply control_as_safe_le with n; eauto. omega.
   case_eq (strip_skip k); intros.
    rewrite <- safeN_strip in H3|-*.  rewrite strip_skip_app in H3|-* by auto.
   rewrite safeN_strip in H3|-*.
    auto.
   assert (ZZ: forall k, strip_skip (c::l++k) = c::l++k)
    by (clear - H5; intros; rewrite <- (strip_skip_app_cons H5); rewrite strip_strip; auto).
  rewrite <- safeN_strip in H3|-*.
  rewrite (strip_skip_app_cons H5) in H3|-* by auto.
  inv H3.
  apply corestep_preservation_lemma
    with (c := c) (l := l) (ve := ve) (te := te) (m := m)
         (ctl1:=ctl1) (ctl2:=ctl2) (n := n') in H8; auto.
   destruct H8 as [? [? [? ?]]].
   econstructor; eauto.
   eapply control_as_safe_le; eauto.
  simpl in H7. congruence.
  simpl in H6. unfold cl_halted in H6. congruence.
Qed.

Lemma guard_safe_adj:
 forall
   psi Delta P k1 k2,
   current_function k1 = current_function k2 ->
  (forall ora m ve te n,
     jsafeN (@OK_spec Espec) psi n ora (State ve te k1) m ->
     jsafeN (@OK_spec Espec) psi n ora (State ve te k2) m) ->
  guard Espec psi Delta P k1 |-- guard Espec psi Delta P k2.
Proof.
intros.
unfold guard.
apply allp_derives. intros tx.
apply allp_derives. intros vx.
rewrite H; apply subp_derives; auto.
intros w ? ? ? ? ?.
apply H0.
eapply H1; eauto.
Qed.

Lemma assert_safe_adj:
  forall ge ve te k k' rho,
      (forall n, control_as_safe ge n k k') ->
     assert_safe Espec ge ve te k rho |-- assert_safe Espec ge ve te k' rho.
Proof.
 intros. intros w ? ? ? ? ?. specialize (H0 ora jm H1 H2).
 eapply H; try apply H0. apply le_refl.
Qed.

Lemma assert_safe_adj':
  forall ge ve te k k' rho P w,
      (forall n, control_as_safe ge n k k') ->
     app_pred (P >=> assert_safe Espec ge ve te k rho) w ->
     app_pred (P >=> assert_safe Espec ge ve te k' rho) w.
Proof.
 intros.
 eapply subp_trans'; [ | apply derives_subp; eapply assert_safe_adj; try eassumption; eauto].
 auto.
Qed.

Lemma rguard_adj:
  forall ge Delta R k k',
      current_function k = current_function k' ->
      (forall ek vl n, control_as_safe ge n (exit_cont ek vl k) (exit_cont ek vl k')) ->
      rguard Espec ge Delta R k |-- rguard Espec ge Delta R k'.
Proof.
 intros.
 intros n H1;  hnf in H1|-*.
 intros ek vl te ve; specialize (H1 ek vl te ve).
 rewrite <- H.
 eapply assert_safe_adj'; eauto.
Qed.


Lemma assert_safe_last': forall (Espec:OracleKind) ge ve te ctl rho w,
            (age1 w <> None -> assert_safe Espec ge ve te ctl rho w) ->
             assert_safe Espec ge ve te ctl rho w.
Proof.
 intros. apply assert_safe_last; intros. apply H. rewrite H0. congruence.
Qed.

Lemma pjoinable_emp_None {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
  forall w: option (psepalg.lifted JA), identity w ->  w=None.
Proof.
intros.
destruct w; auto.
elimtype False.
specialize (H None (Some l)).
spec H.
constructor.
inversion H.
Qed.

Lemma pjoinable_None_emp {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}:
           identity (None: option (psepalg.lifted JA)).
Proof.
intros; intro; intros.
inv H; auto.
Qed.

Lemma unage_mapsto:
  forall sh t v1 v2 w, age1 w <> None -> (|> mapsto sh t v1 v2) w -> mapsto sh t v1 v2 w.
Proof.
  intros.
  case_eq (age1 w); intros; try contradiction.
  clear H.
  specialize (H0 _ (age_laterR H1)).
  unfold mapsto in *.
  revert H0; case_eq (access_mode t); intros; auto.
  destruct (type_is_volatile t); try contradiction.
  destruct v1; try contradiction.
  rename H into Hmode.
  if_tac; rename H into H_READ.
  + destruct H0 as [H0|H0]; [left | right].
    destruct H0 as [H0' H0]; split; auto.
    destruct H0 as [bl [? ?]]; exists bl; split; auto.
    clear - H0 H1.
     intro loc'; specialize (H0 loc').
     hnf in *.
     if_tac.
     destruct H0 as [p ?]; exists p.
     hnf in *.
     rewrite preds_fmap_NoneP in *.
     apply (age1_YES w r); auto.
     unfold noat in *; simpl in *.
    apply <- (age1_resource_at_identity _ _ loc' H1); auto.
    destruct H0 as [? [v2' [bl [? ?]]]].
    hnf in H. subst v2. split; hnf; auto. exists v2', bl; split; auto.
    clear - H2 H1; rename H2 into H0.
     intro loc'; specialize (H0 loc').
     hnf in *.
     if_tac.
     destruct H0 as [p ?]; exists p.
     hnf in *.
     rewrite preds_fmap_NoneP in *.
     apply (age1_YES w r); auto.
     unfold noat in *; simpl in *.
    apply <- (age1_resource_at_identity _ _ loc' H1); auto.
  + split; [exact (proj1 H0) |].
    destruct H0 as [_ ?].
    intro loc'; specialize (H loc').
    hnf in *.
    if_tac.
    - unfold shareat in *; simpl in *.
      pose proof H1.
      apply age1_resource_share with (l := loc') in H1.
      apply age1_nonlock with (l := loc') in H2.
      rewrite H1; tauto.
    - unfold noat in *; simpl in *.
      apply <- (age1_resource_at_identity _ _ loc' H1); auto.
Qed.

Lemma semax_extensionality_Delta {CS: compspecs}:
  forall Delta Delta' P c R,
       tycontext_sub Delta Delta' ->
     semax Espec Delta P c R -> semax Espec Delta' P c R.
Proof.
intros.
unfold semax in *.
intros.
specialize (H0 n).
apply (semax_extensionality1 Espec Delta Delta' P P c R R); auto.
split; auto.
split; auto.
intros ? ? ?; auto.
Qed.

End extensions.

Definition Cnot (e: Clight.expr) : Clight.expr :=
   Clight.Eunop Cop.Onotbool e type_bool.

(* Mutually recursive induction scheme for [statement] and [labeled_statements] *)
Section statement_rect.
  Variable P : statement -> Type.
  Variable Q : labeled_statements -> Type.
  Variable f : P Sskip.
  Variable f0 : forall e e0 : expr, P (Sassign e e0).
  Variable f1 : forall (i : ident) (e : expr), P (Sset i e).
  Variable f2 : forall (o : option ident) (e : expr) (l : list expr), P (Scall o e l).
  Variable f3 : forall (o : option ident) (e : external_function) (t : typelist) (l : list expr), P (Sbuiltin o e t l).
  Variable f4 : forall s : statement, P s -> forall s0 : statement, P s0 -> P (Ssequence s s0).
  Variable f5 : forall (e : expr) (s : statement), P s -> forall s0 : statement, P s0 -> P (Sifthenelse e s s0).
  Variable f6 : forall s : statement, P s -> forall s0 : statement, P s0 -> P (Sloop s s0).
  Variable f7 : P Sbreak.
  Variable f8 : P Scontinue.
  Variable f9 : forall o : option expr, P (Sreturn o).
  Variable f10 : forall (e : expr) (l : labeled_statements), Q l -> P (Sswitch e l).
  Variable f11 : forall (l : label) (s : statement), P s -> P (Slabel l s).
  Variable f12 : forall l : label, P (Sgoto l).
  Variable f13 : Q LSnil.
  Variable f14 : forall (o : option Z) (s : statement) (l : labeled_statements), P s -> Q l -> Q (LScons o s l).

  Fixpoint statement_rect (s : statement) : P s :=
  match s as s0 return (P s0) with
  | Sskip => f
  | Sassign e e0 => f0 e e0
  | Sset i e => f1 i e
  | Scall o e l => f2 o e l
  | Sbuiltin o e t l => f3 o e t l
  | Ssequence s0 s1 => f4 s0 (statement_rect s0) s1 (statement_rect s1)
  | Sifthenelse e s0 s1 => f5 e s0 (statement_rect s0) s1 (statement_rect s1)
  | Sloop s0 s1 => f6 s0 (statement_rect s0) s1 (statement_rect s1)
  | Sbreak => f7
  | Scontinue => f8
  | Sreturn o => f9 o
  | Sswitch e l => f10 e l (labeled_statements_rect l)
  | Slabel l s0 => f11 l s0 (statement_rect s0)
  | Sgoto l => f12 l
  end
  with labeled_statements_rect (l : labeled_statements) : Q l :=
  match l as l0 return (Q l0) with
  | LSnil => f13
  | LScons o s l0 => f14 o s l0 (statement_rect s) (labeled_statements_rect l0)
  end.
End statement_rect.

Require Import VST.msl.eq_dec.

(* Equality is decidable on statements *)
Section eq_dec.
  Local Ltac t := hnf; decide equality; auto.

  Let eq_dec_type := type_eq.
  Let eq_dec_float := Float.eq_dec.
  Let eq_dec_float32 := Float32.eq_dec.
  Let eq_dec_int := Int.eq_dec.
  Let eq_dec_int64 := Int64.eq_dec.
  Let eq_dec_ident := ident_eq.
  Let eq_dec_signature := signature_eq.
  Let eq_dec_attr : EqDec attr. repeat t. Qed.
  Let eq_dec_signedness : EqDec signedness. t. Qed.
  Let eq_dec_intsize : EqDec intsize. t. Qed.
  Let eq_dec_floatsize : EqDec floatsize. t. Qed.
  Let eq_dec_Z : EqDec Z. repeat t. Qed.
  Let eq_dec_calling_convention : EqDec calling_convention. repeat t. Qed.
  Lemma eq_dec_external_function : EqDec external_function. repeat t. Qed.
  Let eq_dec_option_ident := option_eq (ident_eq).
  Let eq_dec_option_Z : EqDec (option Z). repeat t. Qed.
  Let eq_dec_typelist : EqDec typelist. repeat t. Qed.

  Lemma eq_dec_expr : EqDec expr.
  Proof. repeat t. Qed.

  Let eq_dec_expr := eq_dec_expr.
  Let eq_dec_option_expr : EqDec (option expr). repeat t. Qed.
  Let eq_dec_list_expr : EqDec (list expr). repeat t. Qed.

  Local Ltac eq_dec a a' :=
    let H := fresh in
    assert (H : {a = a'} + {a <> a'}) by (auto; repeat (decide equality ; auto));
    destruct H; [subst; auto | try (right; congruence)].

  Lemma eq_dec_statement : forall s s' : statement, { s = s' } + { s <> s' }.
  Proof.
    apply
      (statement_rect
         (fun s => forall s', { s = s' } + { s <> s' })
         (fun l => forall l', { l = l' } + { l <> l' }));
      try (intros until s'; destruct s'); intros;
      try (destruct l');
      try solve [right; congruence | left; reflexivity];
      repeat
        match goal with
        | |- context [ ?x ?a          = ?x ?b          ] => eq_dec a b
        | |- context [ ?x ?y ?a       = ?x ?y ?b       ] => eq_dec a b
        | |- context [ ?x ?a _        = ?x ?b _        ] => eq_dec a b
        | |- context [ ?x ?y ?z ?a    = ?x ?y ?z ?b    ] => eq_dec a b
        | |- context [ ?x ?y ?a _     = ?x ?y ?b _     ] => eq_dec a b
        | |- context [ ?x ?a _  _     = ?x ?b _  _     ] => eq_dec a b
        | |- context [ ?x ?y ?z ?t ?a = ?x ?y ?z ?t ?b ] => eq_dec a b
        | |- context [ ?x ?y ?z ?a _  = ?x ?y ?z ?b _  ] => eq_dec a b
        | |- context [ ?x ?y ?a _  _  = ?x ?y ?b _  _  ] => eq_dec a b
        | |- context [ ?x ?a _  _  _  = ?x ?b _  _  _  ] => eq_dec a b
        end.
  Qed.

  Lemma eq_dec_labeled_statements : forall l l' : labeled_statements, { l = l' } + { l <> l' }.
  Proof.
    decide equality.
    apply eq_dec_statement.
  Qed.

End eq_dec.

Instance EqDec_statement: EqDec statement := eq_dec_statement.
Instance EqDec_external_function: EqDec external_function := eq_dec_external_function.
