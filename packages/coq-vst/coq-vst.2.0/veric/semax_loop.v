Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.seplog.
Require Import VST.veric.assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.semax_congruence.
Require Import VST.veric.Clight_lemmas.

Local Open Scope pred.
Local Open Scope nat_scope.

Section extensions.
Context (Espec : OracleKind).

Lemma funassert_update_tycon:
  forall Delta h, funassert (update_tycon Delta h) = funassert Delta.
intros; apply same_glob_funassert. rewrite glob_specs_update_tycon. auto.
Qed.


Lemma semax_ifthenelse {CS: compspecs}:
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Espec Delta (fun rho => P rho && !! expr_true b rho) c R ->
     semax Espec Delta (fun rho => P rho && !! expr_false b rho) d R ->
     semax Espec Delta
              (fun rho => tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) rho && P rho)
              (Sifthenelse b c d) R.
Proof.
intros.
rewrite semax_unfold in H0, H1 |- *.
intros.
specialize (H0 psi _ _ TS HGG Prog_OK k F).
specialize (H1 psi _ _ TS HGG Prog_OK k F).
spec H0.  {
  intros i te' ?.  apply H2; simpl; auto. intros i0; destruct (H4 i0); intuition.
  left; clear - H5.
 unfold modifiedvars. simpl.
 apply modifiedvars'_union. left; apply H5.
}
spec H1. {
 intros i te' ?.  apply H2; simpl; auto.
 clear - H4; intros i0; destruct (H4 i0); intuition.
 left.
 unfold modifiedvars. simpl.
 apply modifiedvars'_union. right; apply H.
}
assert (H3then: app_pred
       (rguard Espec psi (exit_tycon c Delta')  (frame_ret_assert R F) k) w). {
 clear - H3.
 intros ek vl tx vx; specialize (H3 ek vl tx vx).
 cbv beta in H3.
 eapply subp_trans'; [ | apply H3].
 apply derives_subp; apply andp_derives; auto.
 apply andp_derives; auto.
 unfold exit_tycon; simpl. destruct ek; simpl; auto.
 intros ? [? ?]; split; auto.
 apply typecheck_environ_join1; auto.
 repeat rewrite var_types_update_tycon. auto.
 repeat rewrite glob_types_update_tycon. auto.
 destruct (current_function k); destruct H0; split; auto.
 rewrite ret_type_join_tycon; rewrite ret_type_update_tycon in H1|-*; auto.
 repeat rewrite funassert_exit_tycon in *; auto.
}
assert (H3else: app_pred
       (rguard Espec psi (exit_tycon d Delta') (frame_ret_assert R F) k) w). {
 clear - H3.
 intros ek vl tx vx; specialize (H3 ek vl tx vx).
 eapply subp_trans'; [ | apply H3].
 apply derives_subp; apply andp_derives; auto.
 apply andp_derives; auto.
 unfold exit_tycon; simpl. destruct ek; simpl; auto.
 intros ? [? ?]; split; auto.
 apply typecheck_environ_join2 with Delta'; auto;
  apply tycontext_evolve_update_tycon.
 repeat rewrite var_types_update_tycon. auto.
 repeat rewrite glob_types_update_tycon. auto.
 destruct (current_function k); destruct H0; split; auto.
 rewrite ret_type_join_tycon; rewrite ret_type_update_tycon in H1|-*; auto.
 repeat rewrite funassert_exit_tycon in *; auto.
}
specialize (H0 H3then).
specialize (H1 H3else).
clear Prog_OK H3 H3then H3else.
intros tx vx; specialize (H0 tx vx); specialize (H1 tx vx).
remember (construct_rho (filter_genv psi) vx tx) as rho.
slurp.
rewrite <- fash_and.
intros ? ?. clear w H0.
revert a'.
apply fash_derives.
intros w [? ?].
intros ?w ? [[?TC  ?] ?].
assert (typecheck_environ Delta rho) as TC_ENV. {
  destruct TC as [TC _].
  eapply typecheck_environ_sub; eauto.
}
apply extend_sepcon_andp in H4; auto.
destruct H4 as [TC2 H4].
pose proof TC2 as TC2'.
apply (tc_expr_sub _ _ _ TS) in TC2'; [| auto].
destruct H4 as [w1 [w2 [? [? ?]]]].
specialize (H0 w0 H3).
specialize (H1 w0 H3).
unfold expr_true, expr_false, Cnot in *.
intros ora jm Hge Hphi.
generalize (eval_expr_relate _ _ _ _ _ b jm HGG Hge (guard_environ_e1 _ _ _ TC)); intro.
assert (TCS := typecheck_expr_sound _ _ w0 _ (guard_environ_e1 _ _ _ TC) TC2').
 unfold tc_expr in TC2'.
 simpl in TC2'.
 rewrite denote_tc_assert_andp in TC2'.
 destruct TC2' as [TC2' TC2'a].
assert (exists b': bool, Cop.bool_val (eval_expr b rho) (typeof b) (m_dry jm) = Some b'). {
clear - TS TC H TC2 TC2' TC2'a TCS Hphi.
 simpl in TCS. unfold_lift in TCS.
 unfold Cop.bool_val;
 destruct (eval_expr b rho) eqn:H15;
 simpl; destruct (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
    intuition; simpl in *; try rewrite TCS; eauto.
all: 
rewrite denote_tc_assert_andp in TC2'; destruct TC2' as [TC2'' TC2'];
 rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2';
 simpl in TC2'; unfold_lift in TC2'; rewrite H15 in TC2'.
all: destruct Archi.ptr64 eqn:Hp; try contradiction;
simpl in TC2'; destruct TC2'; subst; eauto;
 rewrite tc_test_eq0; eauto;
 try (eexists; reflexivity).
 simpl; rewrite Hp.
split; auto.
}
clear TCS.
(* typechecking proof *)
destruct H9 as [b' ?].
apply wlog_safeN_gt0; intro.
subst w0.
change (level (m_phi jm)) with (level jm) in H10.
revert H10; case_eq (level jm); intros.
omegaContradiction.
apply levelS_age1 in H10. destruct H10 as [jm' ?].
clear H11.
apply (@safe_step'_back2  _ _ _ _ _ _ _ _ psi ora _ jm
        (State vx tx (Kseq (if b' then c else d) :: k)) jm' _).
split3.
rewrite <- (age_jm_dry H10); econstructor; eauto.
apply age1_resource_decay; auto.
apply age_level; auto.
change (level (m_phi jm)) with (level jm).
replace (level jm - 1)%nat with (level jm' ) by (apply age_level in H10; omega).
eapply @age_safe; try apply H10.
rewrite <- Hge in *.
destruct b'.
*
eapply H0; auto.
split; auto.
split; auto.
rewrite andp_comm.
unfold lift1.
unfold tc_expr in TC2.
 simpl in TC2.
 rewrite denote_tc_assert_andp in TC2.
 destruct TC2 as [TC2 TC2a].
rewrite prop_true_andp.
do 2 econstructor; split3; eauto.
eapply typecheck_expr_sound in TC2a; eauto.
clear - H9 TC2 TC2a.
unfold typed_true, strict_bool_val.
 unfold Cop.bool_val;
 destruct (eval_expr b rho) eqn:H16;
 simpl; destruct (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
   try contradiction;
    intuition; simpl in *; try rewrite TCS; eauto;
try (rewrite denote_tc_assert_andp in TC2; destruct TC2 as [TC2'' TC2]);
 try (rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2;
 simpl in TC2; unfold_lift in TC2; rewrite H16 in TC2);
 destruct Archi.ptr64 eqn:Hp; try contradiction.
simpl in TC2; rewrite Hp in TC2; simpl in TC2; destruct TC2; subst; eauto.
*
eapply H1; auto.
split; auto.
split; auto.
unfold lift1.
rewrite andp_comm; rewrite prop_true_andp.
do 2 econstructor; split3; eauto.
unfold tc_expr in TC2.
 simpl in TC2.
 rewrite denote_tc_assert_andp in TC2.
 destruct TC2 as [TC2 TC2a].
eapply typecheck_expr_sound in TC2a; eauto.
clear - H9 TC2 TC2a.
unfold typed_true, strict_bool_val.
 unfold Cop.bool_val;
 destruct (eval_expr b rho) eqn:H16;
 simpl; destruct (typeof b) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
   try contradiction;
    intuition; simpl in *; try rewrite TCS; eauto;
try (rewrite denote_tc_assert_andp in TC2; destruct TC2 as [TC2'' TC2]);
 try (rewrite binop_lemmas2.denote_tc_assert_test_eq' in  TC2;
 simpl in TC2; unfold_lift in TC2; rewrite H16 in TC2);
 destruct Archi.ptr64 eqn:Hp; try contradiction.
simpl in TC2; rewrite Hp in TC2; simpl in TC2; destruct TC2; subst; eauto.
unfold Cop.bool_val in H9.
unfold typed_false.
unfold classify_bool in H9.
simpl in H9.
rewrite Hp in H9.
if_tac in H9; inv H9.
Qed.
(*
Lemma seq_assoc1:
   forall Delta P s1 s2 s3 R,
        semax Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R ->
        semax Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
rewrite semax_unfold; intros.
intros.
specialize (H psi Delta' w TS Prog_OK k F).
spec H.
intros ? ? ?. apply H0.
intro i; destruct (H2 i); intuition.
spec H; [solve [auto] |].
clear - H.
intros te ve ? ? ? ? ?.
specialize (H te ve y H0 a' H1 H2).
clear - H.
intros ora jm _ H2; specialize (H ora jm (eq_refl _) H2).
clear - H.
destruct (@level rmap ag_rmap a'); simpl in *; auto.
constructor.
inv H.
{ destruct (corestep_preservation_lemma Espec psi
                     (Kseq (Ssequence s2 s3) :: k)
                     (Kseq s2 :: Kseq s3 :: k)
                     ora ve te jm n (Kseq s1) nil c' m')
       as [c2 [m2 [? ?]]]; simpl; auto.
intros. apply control_suffix_safe; simpl; auto.
clear.
intro; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
intros.
destruct H1 as [H1 [H1a H1b]]; split3; auto.  inv H1; auto.
clear.
hnf; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
clear; intros.
destruct H as [H1 [H1a H1b]]; split3; auto.  inv H1; auto.
destruct H1 as (?&?&?). constructor; eauto.
simpl in H|-*. inv H. auto.
destruct H as [H1' [H1a H1b]].
econstructor; eauto.
split3; auto.  inv H1; auto.
do 2 econstructor. auto.
}
simpl in H1. congruence.
simpl in H0. unfold cl_halted in H0. congruence.
Qed.
*)
Ltac inv_safe H :=
  inv H;
  try solve[match goal with
    | H : semantics.at_external _ _ = _ |- _ =>
      simpl in H; congruence
    | H : semantics.halted _ _ = _ |- _ =>
      simpl in H; unfold cl_halted in H; congruence
  end].
(*
Lemma seq_assoc2:
   forall Delta P s1 s2 s3 R,
        semax Espec Delta P (Ssequence (Ssequence s1 s2) s3) R ->
        semax Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R.
Proof.
rewrite semax_unfold; intros.
intros.
specialize (H psi Delta' w TS Prog_OK k F).
spec H.
intros ? ? ?. apply H0.
intro i; destruct (H2 i); intuition.
spec H; [solve [auto] |].
clear - H.
intros te ve ? ? ? ? ?.
specialize (H te ve y H0 a' H1 H2).
clear - H.
intros ora jm _ H2; specialize (H ora jm (eq_refl _) H2).
clear - H.
destruct (@level rmap ag_rmap a'); simpl in *. constructor.
inv_safe H.
destruct (corestep_preservation_lemma Espec psi
                     (Kseq s2 :: Kseq s3 :: k)
                     (Kseq (Ssequence s2 s3) :: k)
                     ora ve te jm n (Kseq s1) nil c' m')
       as [c2 [m2 [? ?]]]; simpl; auto.
intros. apply control_suffix_safe; simpl; auto.
clear.
intro; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
intros.
destruct H1 as [H1 [H1a H1b]]; split3; auto.
constructor; auto.
clear.
hnf; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
clear; intros.
destruct H as [H1 [H1a H1b]]; split3; auto.
constructor; auto.
destruct H1 as (?&?&?). constructor; eauto.
simpl in H|-*. inv H. inv H11. auto.
econstructor; eauto.
destruct H as [H1' [H1a H1b]]; split3; auto.
inv H1. inv H; auto. constructor. auto.
Qed.
*)
Lemma seq_assoc {CS: compspecs}:
  forall Delta P s1 s2 s3 R,
  semax Espec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
  semax Espec Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
intros.
split;
apply semax_unfold_Ssequence;
simpl;
rewrite app_assoc; auto.
Qed.

Lemma semax_seq {CS: compspecs}:
  forall Delta (R: ret_assert) P Q h t,
  semax Espec Delta P h (overridePost Q R) ->
  semax Espec (update_tycon Delta h) Q t R ->
  semax Espec Delta P (Clight.Ssequence h t) R.
Proof.
intros.
rewrite semax_unfold in H,H0|-*.
intros.
specialize (H psi _ w TS HGG Prog_OK).
specialize (H0 psi (update_tycon Delta' h) w).
spec H0. apply update_tycon_sub; auto.
spec H0; auto.
spec H0. {
clear - Prog_OK.
unfold believe in *.
unfold believe_internal in *.
intros v fsig cc A P Q; specialize (Prog_OK v fsig cc A P Q).
intros ? ? ?. specialize (Prog_OK a' H).
spec Prog_OK.
destruct H0 as [id [NEP [NEQ [? ?]]]]. exists id, NEP, NEQ; split; auto.
rewrite glob_specs_update_tycon in H0. auto.
destruct Prog_OK; [ left; auto | right].
destruct H1 as [b [f ?]]; exists b,f.
destruct H1; split; auto.
intro x; specialize (H2 x).
rewrite func_tycontext'_update_tycon.
exact H2.
}
assert ((guard Espec psi Delta' (fun rho : environ => F rho * P rho)%pred
(Kseq h :: Kseq t :: k)) w).
Focus 2. {
eapply guard_safe_adj; try apply H3; try reflexivity;
intros until n; apply convergent_controls_safe; simpl; auto;
intros; destruct q'.
destruct H4 as [? [? ?]]; split3; auto. constructor; auto.
destruct H4 as [? [? ?]]; split3; auto. constructor; auto.
} Unfocus.
eapply H; eauto.
repeat intro; apply H1.
clear - H3. intro i; destruct (H3 i); [left | right]; auto.
unfold modifiedvars in H|-*. simpl. apply modifiedvars'_union.
left; auto.
clear - HGG H0 H1 H2.
intros ek vl.
intros tx vx.
rewrite proj_frame_ret_assert.
destruct (eq_dec ek EK_normal).
*
subst.
unfold exit_cont.
unfold guard in H0.
remember (construct_rho (filter_genv psi) vx tx) as rho.
assert (app_pred
(!!guard_environ (update_tycon Delta' h) (current_function k) rho &&
(F rho * (Q rho)) && funassert Delta' rho >=>
assert_safe Espec psi vx tx (Kseq t :: k) rho) w). {
subst.
specialize (H0 k F).
spec H0.
clear - H1;
repeat intro; apply H1. simpl.
intro i; destruct (H i); [left | right]; auto.
unfold modifiedvars in H0|-*. simpl. apply modifiedvars'_union.
auto.
spec H0.
clear - H2.
intros ek vl te ve; specialize (H2 ek vl te ve).
eapply subp_trans'; [ | apply H2].
apply derives_subp. apply andp_derives; auto.
apply andp_derives; auto.
simpl.
intros ? [? ?]; hnf in H,H0|-*; split; auto.
clear - H.
destruct ek; simpl in *; auto; try solve [eapply typecheck_environ_update; eauto].
destruct (current_function k); destruct H0; split; auto.
rewrite ret_type_exit_tycon in H1|-*; rewrite ret_type_update_tycon in H1; auto.
cbv beta in H2.
repeat rewrite funassert_exit_tycon.
rewrite funassert_update_tycon; auto.
specialize (H0 tx vx). cbv beta in H0.
rewrite funassert_update_tycon in H0.
apply H0.
}
eapply subp_trans'; [ | apply H].
apply derives_subp. apply andp_derives; auto.
 apply andp_derives; auto.
rewrite sepcon_comm;
apply sepcon_derives; auto.
apply andp_left2; auto.
destruct R; simpl; auto.
rewrite funassert_exit_tycon. auto.
*
replace (exit_cont ek vl (Kseq t :: k)) with (exit_cont ek vl k)
by (destruct ek; simpl; congruence).
unfold rguard in H2.
specialize (H2 ek vl tx vx).
replace (exit_tycon h Delta' ek) with Delta'
 by (destruct ek; try congruence; auto).
replace (exit_tycon (Ssequence h t) Delta' ek) with Delta'
  in H2
 by (destruct ek; try congruence; auto).
eapply subp_trans'; [ | apply H2].
apply derives_subp.
apply andp_derives; auto.
apply andp_derives; auto.
rewrite proj_frame_ret_assert.
destruct R, ek; simpl; auto. contradiction n; auto.
Qed.

Lemma control_as_safe_refl psi n k : control_as_safe Espec psi n k k.
Proof.
intros ????? H; inversion 1; subst. constructor.
econstructor; eauto.
simpl in *. congruence.
simpl in H1. unfold cl_halted in H1. congruence.
Qed.

Lemma semax_seq_skip {CS: compspecs}:
  forall Delta P s Q,
  semax Espec Delta P s Q <-> semax Espec Delta P (Ssequence s Sskip) Q.
Proof.
split; intro.
*
rewrite semax_unfold in H|-*.
intros.
specialize (H psi _ _ TS HGG Prog_OK (Kseq Sskip :: k) F H0). clear TS Prog_OK H0.
+
spec H; [clear - H1 | ].
revert w H1; apply rguard_adj; [reflexivity | ].
intros.
destruct ek; simpl; try apply control_as_safe_refl.
repeat intro.
eapply convergent_controls_safe; try apply H0; try reflexivity.
intros. simpl. destruct ret; simpl in *; auto.
intros. simpl in *.
destruct H1 as [? [? ?]]. split3; auto.
constructor. auto.
eapply guard_safe_adj; try apply H; try reflexivity.
intros until n; apply convergent_controls_safe; simpl; auto;
intros; destruct q'.
destruct H0 as [? [? ?]]; split3; auto. constructor; auto.
destruct H0 as [? [? ?]]; split3; auto. constructor; auto.
*
rewrite semax_unfold in H|-*.
intros.
specialize (H psi _ _ TS HGG Prog_OK k F H0 H1). clear TS Prog_OK H0 H1.
eapply guard_safe_adj; try apply H; try reflexivity. clear H.
intros.
destruct n; simpl in *. constructor.
inv_safe H.
destruct (corestep_preservation_lemma Espec psi
          (Kseq Sskip :: k) k ora ve te m n (Kseq s) nil c' m')
  as [c2 [m2 [? ?]]]; simpl; auto.
{ intros. apply control_suffix_safe; simpl; auto.
clear.
intro; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
intros.
destruct H1 as [H1 [H1a H1b]]; split3; auto.
inv H1; auto. }
{ clear.
hnf; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
clear; intros.
destruct H as [H1 [H1a H1b]]; split3; auto.
solve[inv H1; auto]. }
{ destruct H1 as (?&?&?). econstructor; eauto. inv H. auto. }
econstructor; eauto.
Qed.

Lemma semax_skip_seq {CS: compspecs}:
  forall Delta P s Q,
    semax Espec Delta P s Q <-> semax Espec Delta P (Ssequence Sskip s) Q.
Proof.
intros.
split; intro H; rewrite semax_unfold in H|-*; intros;
 specialize (H psi _ _ TS HGG Prog_OK k F H0);
 clear TS Prog_OK H0.
*
spec H. clear H.
revert w H1; apply rguard_adj; [reflexivity | ].
destruct ek; intros; try apply control_as_safe_refl.
clear H1.
revert w H. apply guard_safe_adj; [reflexivity | ].
   intros until n; apply convergent_controls_safe; simpl; auto;
   intros; destruct q'.
   destruct H as [? [? ?]]; split3; auto.
  constructor. constructor. auto.
   destruct H as [? [? ?]]; split3; auto.
   constructor; auto. constructor; auto.
*
spec H. clear H.
revert w H1; apply rguard_adj; [reflexivity | ].
destruct ek; intros; try apply control_as_safe_refl.
clear H1.
revert w H; apply guard_safe_adj; [reflexivity | ].
   intros until n; apply convergent_controls_safe; simpl; auto;
   intros; destruct q'.
   destruct H as [? [? ?]]; split3; auto.
  inv H.  inv H10; auto.
   destruct H as [? [? ?]]; split3; auto.
  inv H. inv H10; auto.
Qed.

Lemma semax_loop {CS: compspecs}:
forall Delta Q Q' incr body R,
     semax Espec Delta Q body (loop1_ret_assert Q' R) ->
     semax Espec Delta Q' incr (loop2_ret_assert Q R) ->
     semax Espec Delta Q (Sloop body incr) R.
Proof.
  intros ? ? ? ? ?  POST H H0.
  rewrite semax_unfold.
  intros until 4.
  rename H1 into H2.
  assert (CLO_body: closed_wrt_modvars body F).
  Focus 1. {
    clear - H2. intros rho te ?. apply (H2 rho te). simpl.
    intro; destruct (H i); auto. left; unfold modifiedvars in H0|-*; simpl;
    apply modifiedvars'_union; auto.
  } Unfocus.
  assert (CLO_incr:  closed_wrt_modvars incr F).
  Focus 1. {
    clear - H2. intros rho te ?. apply (H2 rho te). simpl.
    intro; destruct (H i); auto. left; unfold modifiedvars in H0|-*; simpl;
    apply modifiedvars'_union; auto.
  } Unfocus.
  revert Prog_OK; induction w using (well_founded_induction lt_wf); intros.
  intros tx vx.
  intros ? ? ? ? [[? ?] ?]. hnf in H6.
  simpl update_tycon in H3.
  apply assert_safe_last; intros a2 LEVa2.
  assert (NEC2: necR w (level a2)).
  Focus 1. {
    apply age_level in LEVa2. apply necR_nat in H5. apply nec_nat in H5.
    change w with (level w) in H4|-*. apply nec_nat. clear - H4 H5 LEVa2.
    omega.
  } Unfocus.
  assert (LT: level a2 < level w).
  Focus 1. {
    apply age_level in LEVa2. apply necR_nat in H5.
    clear - H4 H5 LEVa2.
    change w with (level w) in H4.
    change R.rmap with rmap in *.  rewrite LEVa2 in *.  clear LEVa2.
    apply nec_nat in H5. omega.
  } Unfocus.
  assert (Prog_OK2: (believe Espec Delta' psi Delta') (level a2))
    by (apply pred_nec_hereditary with w; auto).
  generalize (pred_nec_hereditary _ _ _ NEC2 H3); intro H3'.
  remember (construct_rho (filter_genv psi) vx tx) as rho.
  pose proof I.
  intros ora jm RE H11.
  pose (H10:=True).
  replace (level a') with (S (level a2))
    by (apply age_level in LEVa2;  rewrite LEVa2; apply minus_n_O).
  subst a'.
  destruct (can_age1_juicy_mem _ _ LEVa2) as [jm' LEVa2'].
  unfold age in LEVa2.
  assert (a2 = m_phi jm').
  Focus 1. {
    generalize (age_jm_phi LEVa2'); unfold age; change R.rmap with rmap.
    change R.ag_rmap with ag_rmap; rewrite LEVa2.
    intro Hx; inv Hx; auto.
  } Unfocus.
  subst a2.
  clear LEVa2; rename LEVa2' into LEVa2.
  apply safe_corestep_backward
   with (State vx tx (Kseq body :: Kseq Scontinue :: Kloop1 body incr :: k))
          jm'.
  Focus 1. {
    split3.
    + rewrite (age_jm_dry LEVa2); econstructor.
    + apply age1_resource_decay; auto.
    + apply age_level; auto.
  } Unfocus.
  eapply semax_extensionality_Delta in H; try apply TS; auto.
  eapply semax_extensionality_Delta in H0; try apply TS; auto.
  clear Delta TS.
  assert (w >= level (m_phi jm)).
  Focus 1. {
    apply necR_nat in H5. apply nec_nat in H5.
    change R.rmap with rmap in *; omega.
  } Unfocus.
  clear y H5 H4. rename H11 into H5. pose (H4:=True).
  generalize H; rewrite semax_unfold; intros H'.
  change ((believe Espec Delta' psi Delta') (level jm')) in Prog_OK2.
  specialize (H' psi Delta' (level jm') (tycontext_sub_refl _) HGG Prog_OK2 (Kseq Scontinue :: Kloop1 body incr :: k) F CLO_body).
  spec H'.
  Focus 2. {
    apply (H' tx vx _ (le_refl _) (m_phi jm') (necR_refl _)); try solve[subst; auto].
    apply pred_hereditary with (m_phi jm); auto.
    + apply age_jm_phi; auto.
    + subst.
      split; auto.
      split; auto.
  } Unfocus.
  intros ek vl.
  destruct ek.
  + simpl exit_cont.
    rewrite semax_unfold in H0.
    specialize (H0 psi _ (level jm') (tycontext_sub_refl _)  HGG Prog_OK2 (Kloop2 body incr :: k) F CLO_incr).
    spec H0.
    Focus 1. {
      intros ek2 vl2 tx2 vx2.
      destruct ek2; simpl exit_tycon in *.
      + unfold exit_cont.
        apply (assert_safe_adj' Espec) with (k:=Kseq (Sloop body incr) :: k); auto.
        - repeat intro. eapply convergent_controls_safe; try apply H12; simpl; auto.
          intros q' m' [? [? ?]]; split3; auto. inv H13; econstructor; eauto.
        - eapply subp_trans'; [ |  eapply (H1 _ LT Prog_OK2 H3' tx2 vx2)].
          apply derives_subp.
          rewrite funassert_update_tycon.
          apply andp_derives; auto.
          apply andp_derives; auto.
          * intros ? [? ?]; split; auto.
            hnf in H11|-*.
            eapply typecheck_environ_update; eauto.
            simpl in H12|-*. rewrite ret_type_update_tycon in H12; auto.
          * simpl exit_cont.
            rewrite proj_frame_ret_assert. simpl proj_ret_assert. simpl seplog.sepcon.
            normalize.
            rewrite sepcon_comm. destruct POST; simpl; auto.
      + rewrite proj_frame_ret_assert. simpl seplog.sepcon.
        destruct POST; simpl tycontext.RA_break. cbv zeta. normalize.
      + rewrite proj_frame_ret_assert. simpl seplog.sepcon.
        destruct POST; simpl tycontext.RA_continue. cbv zeta. normalize.
      + rewrite proj_frame_ret_assert.
        change (exit_cont EK_return vl2 (Kloop2 body incr :: k))
          with (exit_cont EK_return vl2 k).
        eapply subp_trans'; [ | apply H3'].
        rewrite proj_frame_ret_assert.
        clear. simpl exit_tycon. simpl current_function. simpl proj_ret_assert.
        destruct POST; simpl tycontext.RA_return.
        apply subp_refl'.
    } Unfocus.
    intros tx2 vx2.
    apply (assert_safe_adj' Espec) with (k:= Kseq incr :: Kloop2 body incr :: k); auto.
    intros ? ? ? ? ? ? ?.
    eapply convergent_controls_safe; simpl; eauto.
    intros q' m' [? [? ?]]; split3; auto. constructor. simpl. auto.
    eapply subp_trans'; [ | apply H0].
    apply derives_subp.
    unfold frame_ret_assert.
    rewrite funassert_exit_tycon.
    apply andp_derives; auto.
    apply andp_derives; auto.
    - simpl exit_tycon.
      intros ? [? ?]; split.
      * hnf in H11|-*.
        eapply typecheck_environ_update; eauto.
      * simpl in H12|-*; rewrite ret_type_update_tycon in H12; auto.
    - simpl exit_cont.
      simpl exit_tycon.
      rewrite sepcon_comm. destruct POST; simpl proj_ret_assert. normalize.
  + intros tx3 vx3.
    rewrite proj_frame_ret_assert. simpl proj_ret_assert.
    simpl seplog.sepcon. cbv zeta.
    eapply subp_trans'; [ | apply (H3' EK_normal None tx3 vx3)].
    simpl exit_tycon. rewrite proj_frame_ret_assert. simpl current_function.
    destruct POST; simpl tycontext.RA_break; simpl proj_ret_assert.
    apply derives_subp. simpl seplog.sepcon.
    apply andp_derives; auto. apply andp_derives; auto. normalize.
  + simpl exit_tycon. simpl exit_cont.
    rewrite proj_frame_ret_assert.
    intros tx2 vx2. cbv zeta. simpl seplog.sepcon.
    destruct POST; simpl tycontext.RA_continue.
    rewrite semax_unfold in H0.
    eapply subp_trans'; [ | apply (H0 _ _ _ (tycontext_sub_refl _) HGG Prog_OK2 (Kloop2 body incr :: k) F CLO_incr)].
    Focus 1. {
      apply derives_subp.
      apply andp_derives; auto.
      rewrite sepcon_comm.
      apply andp_derives; auto. normalize; auto.
    } Unfocus.
    clear tx2 vx2.
    intros ek2 vl2 tx2 vx2.
    destruct ek2.
    unfold exit_cont.
    apply (assert_safe_adj' Espec) with (k:=Kseq (Sloop body incr) :: k); auto.
    - intros ? ? ? ? ? ? ?.
      eapply convergent_controls_safe; simpl; eauto.
      intros q' m' [? [? ?]]; split3; auto. inv H12; econstructor; eauto.
    - eapply subp_trans'; [ | eapply H1; eauto].
      apply derives_subp.
      rewrite funassert_exit_tycon;
      apply andp_derives; auto.
      apply andp_derives; auto.
      * simpl exit_tycon.
        intros ? [? ?]; split.
        hnf in H11|-*.
        eapply typecheck_environ_update; eauto.
        simpl in H12|-*; rewrite ret_type_update_tycon in H12; auto.
      * unfold exit_cont, loop2_ret_assert; normalize.
        specialize (H3' EK_return vl2 tx2 vx2). simpl exit_tycon in H3'.
        intros tx4 vx4.
        rewrite proj_frame_ret_assert in H3', vx4.
        simpl seplog.sepcon in H3',vx4. cbv zeta in H3', vx4.
        normalize in vx4.        
        rewrite sepcon_comm; auto.
    - intros tx4 vx4. simpl frame_ret_assert in *. simpl proj_ret_assert in *.
      normalize. 
      unfold loop2_ret_assert. normalize.
      repeat intro; normalize.
    - simpl proj_ret_assert in H3'|-*. cbv zeta. normalize.
    - simpl proj_ret_assert in H3'|-*. cbv zeta. 
      simpl exit_tycon.
      specialize (H3' EK_return vl2).
      eapply subp_trans'; [ | eapply H3'; eauto].
      auto.
  + intros tx4 vx4. cbv zeta.
    eapply subp_trans'; [ | eapply (H3' EK_return) ; eauto].
     simpl exit_tycon.
    simpl proj_ret_assert. destruct POST; simpl tycontext.RA_return.
    apply subp_refl'.
Qed.

Lemma semax_break {CS: compspecs}:
   forall Delta Q,        semax Espec Delta (RA_break Q) Sbreak Q.
Proof.
  intros.
  rewrite semax_unfold; intros.  clear Prog_OK. rename w into n.
  intros te ve w ?.
  specialize (H0 EK_break None te ve w H1).
  simpl exit_cont in H0.
  clear n H1.
  remember ((construct_rho (filter_genv psi) ve te)) as rho.
  revert w H0.
  apply imp_derives; auto.
  apply andp_derives; auto.
  repeat intro. simpl exit_tycon.
  rewrite proj_frame_ret_assert. simpl proj_ret_assert; simpl seplog.sepcon.
  rewrite (prop_true_andp (None=None)) by auto.
  rewrite sepcon_comm.
  eapply andp_derives; try apply H0; auto.
  repeat intro.
  specialize (H0 ora jm H1 H2).
  destruct (@level rmap _ a). constructor.
  apply convergent_controls_safe with (State ve te (break_cont k)); auto.
  simpl.

  intros.
  destruct H3 as [? [? ?]].
  split3; auto.

  econstructor; eauto.
Qed.

Lemma semax_continue {CS: compspecs}:
   forall Delta Q,        semax Espec Delta (RA_continue Q) Scontinue Q.
Proof.
 intros.
 rewrite semax_unfold; intros.  clear Prog_OK. rename w into n.
 intros te ve w ?.
 specialize (H0 EK_continue None te ve w H1).
 simpl exit_cont in H0.
 clear n H1.
 remember ((construct_rho (filter_genv psi) ve te)) as rho.
 revert w H0.
apply imp_derives; auto.
apply andp_derives; auto.
repeat intro. simpl exit_tycon.
  rewrite proj_frame_ret_assert. simpl proj_ret_assert; simpl seplog.sepcon.
  rewrite (prop_true_andp (None=None)) by auto.
rewrite sepcon_comm.
eapply andp_derives; try apply H0; auto.
repeat intro.
specialize (H0 ora jm H1 H2).
destruct (@level rmap _ a). constructor.
apply convergent_controls_safe with (State ve te (continue_cont k)); auto.
simpl.

intros.
destruct H3 as [? [? ?]].
split3; auto.

econstructor; eauto.
Qed.

End extensions.
