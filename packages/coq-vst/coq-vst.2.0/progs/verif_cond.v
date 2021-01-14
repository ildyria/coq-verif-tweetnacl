Require Import VST.progs.conclib.
Require Import VST.progs.cond.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition acquire_spec := DECLARE _acquire acquire_spec.
Definition release_spec := DECLARE _release release_spec.
Definition makelock_spec := DECLARE _makelock (makelock_spec _).
Definition freelock_spec := DECLARE _freelock (freelock_spec _).
Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition freelock2_spec := DECLARE _freelock2 (freelock2_spec _).
Definition release2_spec := DECLARE _release2 release2_spec.
Definition makecond_spec := DECLARE _makecond (makecond_spec _).
Definition freecond_spec := DECLARE _freecond (freecond_spec _).
Definition wait_spec := DECLARE _waitcond (wait_spec _).
Definition signal_spec := DECLARE _signalcond (signal_spec _).

Definition dlock_inv data := EX i : Z, data_at Ews tint (vint i) data.

Definition tlock_inv sh lockt lock cond data :=
  selflock (cond_var sh cond * lock_inv sh lock (dlock_inv data)) sh lockt.

Definition thread_func_spec :=
 DECLARE _thread_func
  WITH y : val, x : val * share * val * val * val
  PRE [ _args OF (tptr tvoid) ]
         let '(data, sh, lock, lockt, cond) := x in
         PROP  ()
         LOCAL (temp _args y; gvar _data data; gvar _mutex lock; gvar _tlock lockt;
                gvar _cond cond)
         SEP   ((!!readable_share sh && emp); cond_var sh cond;
                lock_inv sh lock (dlock_inv data);
                lock_inv sh lockt (tlock_inv sh lockt lock cond data))
  POST [ tptr tvoid ]
         PROP ()
         LOCAL ()
         SEP (emp).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ] main_post prog nil u.

Definition Gprog : funspecs :=   ltac:(with_library prog [acquire_spec; release_spec; release2_spec; makelock_spec;
  freelock_spec; freelock2_spec; spawn_spec; makecond_spec; freecond_spec; wait_spec; signal_spec;
  thread_func_spec; main_spec]).

Lemma inv_precise : forall p,
  precise (dlock_inv p).
Proof.
  intro; eapply derives_precise, data_at__precise with (sh := Ews)(t := tint); auto.
  intros ? (? & H); apply data_at_data_at_ in H; eauto.
Qed.

Lemma inv_positive : forall ctr,
  positive_mpred (dlock_inv ctr).
Proof.
  intro; apply ex_positive; auto.
Qed.
Hint Resolve inv_precise inv_positive.

Lemma body_thread_func : semax_body Vprog Gprog f_thread_func thread_func_spec.
Proof.
  start_function.
  Intros.
  forward.
  forward.
  forward.
  forward_call (lock, sh, dlock_inv data).
  unfold dlock_inv; simpl.
  Intro i.
  forward.
  forward_call (cond, sh).
  rewrite field_at_isptr; Intros.
  forward_call (lock, sh, dlock_inv data).
  { lock_props.
    unfold dlock_inv; Exists 1; cancel. }
  rewrite cond_var_isptr; Intros.
  forward_call (lockt, sh, cond_var sh cond * lock_inv sh lock (dlock_inv data),
                tlock_inv sh lockt lock cond data).
  { unfold tlock_inv; lock_props.
    - apply selflock_precise, precise_sepcon; auto.
    - rewrite sepcon_comm; apply selflock_rec.
    - rewrite selflock_eq at 2; cancel.
      eapply derives_trans; [apply lock_inv_later | cancel]. }
  forward.
Qed.

Lemma lock_struct : forall p, data_at_ Ews (Tstruct _lock_t noattr) p |-- data_at_ Ews tlock p.
Proof.
  intros.
  unfold data_at_, field_at_, field_at; simpl; entailer.
  unfold default_val; simpl.
  rewrite data_at_rec_eq; simpl.
  unfold struct_pred, aggregate_pred.struct_pred, at_offset, withspacer; simpl; entailer.
  (* temporarily broken *)
Admitted.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
  name lock _mutex; name lockt _tlock; name cond _cond; name data _data.
  start_function.
  forward.
  forward.
  forward.
  forward.
  forward_call (cond, Ews).
  { unfold tcond; entailer!. }
  rewrite field_at_isptr; Intros.
  destruct split_Ews as (sh1 & sh2 & ? & ? & Hsh).
  forward_call (lock, Ews, dlock_inv data).
  { rewrite (sepcon_comm _ (fold_right_sepcon _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  forward_call (lockt, Ews, tlock_inv sh1 lockt lock cond data).
  { rewrite (sepcon_comm _ (fold_right_sepcon _)); apply sepcon_derives; [cancel | apply lock_struct]. }
  get_global_function'' _thread_func.
  apply extract_exists_pre; intros f_.
  forward_spawn (val * share * val * val * val)%type (f_, Vint (Int.repr 0),
    fun x : val * share * val * val * val => let '(data, sh, lock, lockt, cond) := x in
      [(_data, data); (_mutex, lock); (_tlock, lockt); (_cond, cond)], (data, sh1, lock, lockt, cond),
    fun (x : (val * share * val * val * val)) (_ : val) => let '(data, sh, lock, lockt, cond) := x in
         !!readable_share sh && emp * cond_var sh cond * lock_inv sh lock (dlock_inv data) *
         lock_inv sh lockt (tlock_inv sh lockt lock cond data)).
  { simpl spawn_pre; entailer!.
    { erewrite gvar_eval_var, !(force_val_sem_cast_neutral_gvar' _ f_) by eauto.
      split; auto; repeat split; apply gvar_denote_global; auto. }
    Exists _args; entailer!.
    rewrite !sepcon_assoc; apply sepcon_derives.
    { apply derives_refl'. f_equal.
      f_equal; extensionality.
      destruct x as (?, x); repeat destruct x as (x, ?); simpl.
      extensionality; apply mpred_ext; entailer!. }
    erewrite <- lock_inv_share_join; try apply Hsh; auto.
    erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto.
    erewrite <- cond_var_share_join; try apply Hsh; auto.
    entailer!. }
  forward.
  forward_while (EX i : Z, PROP ( )
   LOCAL (temp _v (Vint (Int.repr i)); temp _c cond; temp _t lockt; temp _l lock; gvar _data data;
     gvar _cond cond; gvar _tlock lockt; gvar _mutex lock)
   SEP (lock_inv sh2 lockt (tlock_inv sh1 lockt lock cond data);
        lock_inv sh2 lock (dlock_inv data); cond_var sh2 cond; dlock_inv data)).
  { Exists 0; entailer!.
    Exists 0; entailer. }
  { entailer. }
  - (* loop body *)
    forward_call (cond, lock, sh2, sh2, dlock_inv data).
    unfold dlock_inv; Intro i'.
    forward.
    unfold dlock_inv; Exists i'; entailer!.
    Exists i'; entailer!.
  - forward_call (lockt, sh2, tlock_inv sh1 lockt lock cond data).
    forward_call (lockt, Ews, sh1, |>(cond_var sh1 cond * lock_inv sh1 lock (dlock_inv data)),
                  |>tlock_inv sh1 lockt lock cond data).
    { unfold tlock_inv; lock_props.
      + apply later_positive; auto.
      + unfold rec_inv.
        rewrite selflock_eq at 1.
        rewrite later_sepcon; f_equal.
        apply lock_inv_later_eq.
      + rewrite selflock_eq at 2.
        erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel.
        rewrite !sepcon_assoc; eapply sepcon_derives; [apply lock_inv_later | cancel]. }
    forward_call (lock, Ews, dlock_inv data).
    { lock_props.
      erewrite <- (lock_inv_share_join _ _ Ews); try apply Hsh; auto; cancel. }
    forward_call (cond, Ews).
    { erewrite !sepcon_assoc, cond_var_share_join; eauto; cancel. }
    forward.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_thread_func.
semax_func_cons body_main.
Qed.
