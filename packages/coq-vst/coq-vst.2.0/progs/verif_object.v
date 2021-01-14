Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.progs.object.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Local Open Scope Z.
Local Open Scope logic.

Definition object_invariant := list Z -> val -> mpred.

Definition tobject := tptr (Tstruct _object noattr).

Definition reset_spec (instance: object_invariant) :=
  WITH self: val, history: list Z
  PRE [ _self OF tobject]
          PROP ()
          LOCAL (temp _self self)
          SEP (instance history self)
  POST [ tvoid ]
          PROP() LOCAL () SEP(instance nil self).

Definition twiddle_spec (instance: object_invariant) :=
  WITH self: val, i: Z, history: list Z
  PRE [ _self OF tobject, _i OF tint]
          PROP (0 < i <= Int.max_signed / 4;
                0 <= fold_right Z.add 0 history <= Int.max_signed / 4)
          LOCAL (temp _self self; temp _i (Vint (Int.repr i)))
          SEP (instance history self)
  POST [ tint ]
      EX v: Z, 
          PROP(2* fold_right Z.add 0 history < v <= 2* fold_right Z.add 0 (i::history))
          LOCAL (temp ret_temp (Vint (Int.repr v))) 
          SEP(instance (i::history) self).

Definition object_methods (instance: object_invariant) (mtable: val) : mpred :=
  EX sh: share, EX reset: val, EX twiddle: val,
  !! readable_share sh && 
  func_ptr' (reset_spec instance) reset *
  func_ptr' (twiddle_spec instance) twiddle *
  data_at sh (Tstruct _methods noattr) (reset,twiddle) mtable.

Lemma object_methods_local_facts: forall instance p,
  object_methods instance p |-- !! isptr p.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle.
entailer!.
Qed.
Hint Resolve object_methods_local_facts : saturate_local.

Definition object_mpred (history: list Z) (self: val) : mpred :=
  EX instance: object_invariant, EX mtable: val, 
       (object_methods instance mtable *
     field_at Tsh (Tstruct _object noattr) [StructField _mtable] mtable self*
     instance history self).

Definition foo_invariant : object_invariant :=
  (fun (history: list Z) p => field_at Tsh (Tstruct _foo_object noattr) 
            [StructField _data] (Vint (Int.repr (2*fold_right Z.add 0 history))) p
      *  malloc_token Tsh (sizeof (Tstruct _foo_object noattr)) p).

Definition foo_reset_spec :=
 DECLARE _foo_reset (reset_spec foo_invariant).

Definition foo_twiddle_spec :=
 DECLARE _foo_twiddle  (twiddle_spec foo_invariant).

Definition make_foo_spec :=
 DECLARE _make_foo
 WITH mtable: val
 PRE [ ]
    PROP () LOCAL (gvar _foo_methods mtable) 
    SEP (object_methods foo_invariant mtable)
 POST [ tobject ]
    EX p: val, PROP () LOCAL (temp ret_temp p)
     SEP (object_mpred nil p; object_methods foo_invariant mtable).

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ]
     EX i:Z, PROP(0<=i<=6) LOCAL (temp ret_temp (Vint (Int.repr i))) SEP(TT).

Definition Gprog : funspecs :=   ltac:(with_library prog [
    foo_reset_spec; foo_twiddle_spec; make_foo_spec; main_spec]).

Lemma body_foo_reset: semax_body Vprog Gprog f_foo_reset foo_reset_spec.
Proof.
unfold foo_reset_spec, foo_invariant, reset_spec.
start_function.
simpl.
Intros.
forward.  (* self->data=0; *)
forward.  (* return; *)
Qed.

Lemma body_foo_twiddle: semax_body Vprog Gprog f_foo_twiddle foo_twiddle_spec.
Proof.
unfold foo_twiddle_spec, foo_invariant, twiddle_spec.
start_function.
Intros.
forward.  (* d = self->data; *)
forward.  (* self -> data = d+2*i; *) 
 set (j:= Int.max_signed / 4) in *; compute in j; subst j.
 forget (fold_right Z.add 0 history) as h.
 entailer!.
forward.  (* return d+i; *)
 set (j:= Int.max_signed / 4) in *; compute in j; subst j.
 forget (fold_right Z.add 0 history) as h.
 entailer!.
Exists (2 * fold_right Z.add 0 history + i).
rewrite Z.mul_add_distr_l, Z.add_comm.
entailer!.
Qed.

Lemma split_object_methods:
  forall instance m, 
    object_methods instance m |-- object_methods instance m * object_methods instance m.
Proof.
intros.
unfold object_methods.
Intros sh reset twiddle.
Exists (fst (Share.split sh)) reset twiddle.
Exists (snd (Share.split sh)) reset twiddle.
rewrite (split_func_ptr' (reset_spec instance) reset) at 1.
rewrite (split_func_ptr' (twiddle_spec instance) twiddle) at 1.
entailer!.
split.
apply slice.split_YES_ok1; auto.
apply slice.split_YES_ok2; auto.
rewrite (data_at_share_join (fst (Share.split sh)) (snd (Share.split sh)) sh).
auto.
apply split_join.
destruct (Share.split sh) as [a b]; reflexivity.
Qed.

Lemma body_make_foo: semax_body Vprog Gprog f_make_foo make_foo_spec.
Proof.
unfold make_foo_spec.
start_function.
forward_call (sizeof (Tstruct _foo_object noattr)).
   simpl; computable.
Intros p.
forward_if
  (PROP ( )
   LOCAL (temp _p p; gvar _foo_methods mtable)
   SEP (malloc_token Tsh (sizeof (Tstruct _foo_object noattr)) p;
          memory_block Tsh (sizeof (Tstruct _foo_object noattr)) p;
          object_methods foo_invariant mtable)).
*
change (Memory.EqDec_val p nullval) with (eq_dec p nullval).
if_tac; entailer.
*
forward_call tt.
contradiction.
*
rewrite if_false by (intro; subst; inv H).
Intros.
forward.  (*  /*skip*/;  *)
entailer!.
*
assert_PROP (field_compatible (Tstruct _foo_object noattr) [] p).
  entailer!.
rewrite memory_block_data_at_ by auto.
unfold data_at_, field_at_, default_val; simpl.
forward. (* p->mtable = &foo_methods; *)
forward. (* p->data = 0; *)
forward. (* return (struct object * ) p; *)
Exists p.
unfold object_mpred.
Exists foo_invariant mtable.
sep_apply (split_object_methods foo_invariant mtable).
unfold foo_invariant at 4.
entailer!.
simpl.
unfold_field_at 1%nat.
cancel.
rewrite !field_at_data_at.
simpl.
apply derives_refl'.
f_equal.
rewrite !field_compatible_field_address; auto with field_compatible.
clear - H.
(* TODO: simplify the following proof. *)
destruct H as [? [? [SZ [AL ?]]]].
repeat split; auto.
hnf in SZ|-*. destruct p; auto; simpl in SZ|-*; omega.
hnf in AL|-*. destruct p; auto; unfold align_compatible in AL|-*.
eapply align_compatible_rec_Tstruct; [reflexivity |].
simpl co_members; intros.
simpl in H2.
if_tac in H2; [| inv H2].
inv H2.
subst.
inv H3.
eapply align_compatible_rec_Tstruct_inv' with (i0 := _mtable) in AL; [| left; auto].
exact AL.
simpl.
left; auto.
Qed.

Lemma body_main:  semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
rename v_foo_methods into mtable;
rename v_foo_twiddle into twiddle;
rename v_foo_reset into reset.
fold noattr cc_default.

(* 1. Prove that [mtable] is a proper method-table for foo-objects *)
make_func_ptr _foo_twiddle.
make_func_ptr _foo_reset.
gather_SEP 0 1 2 3.
replace_SEP 0 (object_methods foo_invariant mtable). {
  entailer!.
  unfold object_methods.
  Exists Ews reset twiddle.
  entailer!.
  unfold_data_at 1%nat.
  rewrite <- mapsto_field_at with (v:=reset) by auto with field_compatible.
  rewrite <- mapsto_field_at with (v:=twiddle) by auto with field_compatible.
  rewrite !field_compatible_field_address by auto with field_compatible.
  rewrite !isptr_offset_val_zero by auto.
  rewrite sepcon_comm.
  apply derives_refl.
}
drop_LOCALs [_foo_twiddle; _foo_reset].
clear reset twiddle.
(* Finished proving that [mtable] is a proper [object_methods] for foo *)

(* 2. Build an instance of class [foo], called [p] *)
forward_call (* p = make_foo(); *)
        mtable.
Intros p.

(* 3. We can do these next 3 lines because we won't create any more foo objects *)
drop_LOCALs [_foo_methods].
forget (object_methods foo_invariant mtable) as MT. 
clear mtable.

(* 4. first method-call *)
unfold object_mpred.
Intros instance mtable0.
forward. (*  mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0.
forward. (* p_reset = mtable->reset; *)
forward_call (* p_reset(p); *)
      (p, @nil Z).
(* Finish the method-call by regathering the object p back together *)
gather_SEP 1 2 3.
replace_SEP 0 (object_methods instance mtable0). {
  unfold object_methods.
  entailer!. Exists sh r0 t0. entailer!.
}
gather_SEP 0 1 2.
replace_SEP 0 (object_mpred nil p). {
  unfold object_mpred; entailer!.
 Exists instance mtable0; entailer!.
}
drop_LOCALs [_p_reset; _mtable]. clear sh H r0 t0 mtable0 instance.

(* 5. second method-call *)
unfold object_mpred.
Intros instance mtable0.
forward.  (* mtable = p->mtable; *)
unfold object_methods at 1.
Intros sh r0 t0.
forward.   (* p_twiddle = mtable->twiddle; *)
forward_call (* i = p_twiddle(p,3); *)
      (p, 3, @nil Z).
  simpl. computable.
Intros i.
simpl in H0.
(* Finish the method-call by regathering the object p back together *)
gather_SEP 1 2 3.
replace_SEP 0 (object_methods instance mtable0). {
  unfold object_methods.
  entailer!. Exists sh r0 t0. entailer!.
}
gather_SEP 0 1 2.
replace_SEP 0 (object_mpred [3] p). {
  unfold object_mpred; entailer!. Exists instance mtable0; entailer!.
}
drop_LOCALs [_p_twiddle; _mtable]. clear sh H r0 t0 mtable0 instance.

(* 6. return *)
forward.  (* return i; *)
Exists i; entailer!.
Qed.





