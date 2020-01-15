Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.M.

Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_car25519.
Require Import Tweetnacl_verif.spec_M.
Require Import Tweetnacl_verif.verif_M_compute.
Require Import Tweetnacl_verif.verif_M_lemmas.

Open Scope Z.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs := 
      ltac:(with_library prog [car25519_spec; M_spec]).

Lemma body_M: semax_body Vprog Gprog f_M M_spec.
Proof.
start_function.
unfold Sfor.
freeze [1] F.
freeze_local L.
forward_for_simple_bound 31 (M_Tinit_Inv F L v_t) ; subst L.
thaw_local.
- entailer!.
- forward ; rewrite M.lemma_t_defined ; try omega.
  entailer!.
- rewrite M.t_31_0.
  remember [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
                0; 0; 0; 0; 0] as t.
  assert (Zlength t = 31) by (subst t ; reflexivity).
  (*OUTER LOOP*)
  thaw F.
  freeze_local L.
  forward_for_simple_bound 16 (M1_outer_Inv sho sha shb L v_o v_a v_b v_t o a b t k) ; subst L.
  thaw_local.
  + rewrite outer_M_fix_0.
    entailer!.
  +
  1:{
  assert(Haux1: exists aux1, Vlong aux1 = Znth i (mVI64 a) Vundef)
    by (erewrite (Znth_map Int64.zero) ; [eexists ; reflexivity | rewrite Zlength_map; go]).
  assert(Haux: forall j, 0 <= j < 16 -> exists aux, Vlong aux = Znth (i + j) (map Vlong (map Int64.repr (outer_M_fix i j a b t))) Vundef)
    by (intros ; erewrite (Znth_map Int64.zero); [eexists; reflexivity|rewrite Zlength_map outer_M_fix_Zlength] ; omega).
  assert(Haux2: forall j, 0 <= j < 16 -> exists aux2, Vlong aux2 = Znth j (map Vlong (map Int64.repr b)) Vundef)
    by (intros; erewrite (Znth_map Int64.zero); [eexists; reflexivity | rewrite Zlength_map]; omega).
  rewrite /nm_overlap_array_sep_3 ; flatten; Intros.
  all: destruct Haux1 as [aux1 Haux1].
  1: subst o v_o.
  2: subst o v_o.
  3: subst b v_b.
  4: subst o a v_o v_a.



(*   all: forward ; rewrite -Haux1.
  1,3,5,7,9: entailer!.
 *)
   Ltac solve_first_loop_last i :=   rewrite /nm_overlap_array_sep_3 /nm_overlap_array_sep_3'; repeat match goal with 
  | [ H : (_ =? _ ) = true |- _ ] => rewrite H
  | [ H : (_ =? _ ) = false |- _ ] => rewrite H
  end;
  rewrite (outer_M_fix_equation (i + 1));
  destruct ( i + 1 <=? 0) eqn:Heq0; try apply Zle_bool_imp_le in Heq0 ; try omega;
  replace (i + 1 - 1) with i by omega;
  rewrite inner_M_fix_equation; entailer!.
  1: forward_for_simple_bound 16 (M1_inner_Inv sho sha shb v_a v_a v_b v_t i (mVI64 a) a b t 0); 
  [unfold nm_overlap_array_sep_3 ; entailer! | | solve_first_loop_last i].
  2: forward_for_simple_bound 16 (M1_inner_Inv sho sha shb v_b v_a v_b v_t i (mVI64 b) a b t 1);
  [unfold nm_overlap_array_sep_3 ; entailer! | | solve_first_loop_last i].
  3: forward_for_simple_bound 16 (M1_inner_Inv sho sha shb v_o v_a v_a v_t i o a a t 2);
  [unfold nm_overlap_array_sep_3 ; entailer! | | solve_first_loop_last i].
  4: forward_for_simple_bound 16 (M1_inner_Inv sho sha shb v_b v_b v_b v_t i (mVI64 b) b b t 3);
  [unfold nm_overlap_array_sep_3 ; entailer! | | solve_first_loop_last i].
  5: forward_for_simple_bound 16 (M1_inner_Inv sho sha shb v_o v_a v_b v_t i o a b t 4);
  [unfold nm_overlap_array_sep_3 ; entailer! | | solve_first_loop_last i].
  all: rewrite /nm_overlap_array_sep_3 ; simpl; Intros.
  all: rename i0 into j ; rename H6 into Hj.
  all: destruct (Haux j Hj) as [aux HHaux].
  all: destruct (Haux2 j Hj) as [aux2 HHaux2].
  all: forward ; rewrite -HHaux.
  1,3,5,7,9: entailer!.
  all: forward ; rewrite -Haux1.
  1,3,5,7,9: entailer!.
  all: forward ; rewrite -HHaux2.
  1,3,5,7,9: entailer!.
  all: forward ; entailer!.
  1,3,5,7,9: clean_context_from_VST.
  1,2,3,4,5: rewrite ?map_map in Haux1.
  1,2,3,4,5: rewrite ?map_map in HHaux2.
  1,2,3,4,5: rewrite ?map_map in HHaux.
  1,2,3,4,5: rewrite (Znth_map 0) in Haux1.
  2,4,6,8,10: omega.
  1,2,3,4,5: rewrite (Znth_map 0) in HHaux2.
  2,4,6,8,10: omega.
  1,2,3,4,5: rewrite (Znth_map 0) in HHaux.
  2,4,6,8,10: rewrite outer_M_fix_Zlength ; omega.
  1,2,3,4,5: assert(InjVlong: forall a b, Vlong a = Vlong b -> a = b) by congruence.
  1,2,3,4,5: apply InjVlong in HHaux.
  1,2,3,4,5: apply InjVlong in HHaux2.
  1,2,3,4,5: apply InjVlong in Haux1.
  1,2,3,4,5: rewrite HHaux.
  1,2,3,4,5: rewrite Haux1.
  1,2,3,4,5: rewrite HHaux2.
  1,2,3,4,5: rewrite mul64_repr.
  all: try assert(HZntha1: - 2 ^ 26 < Znth i a 0 < 2 ^ 26) by solve_bounds_by_values_Znth.
  all: try assert(HZntha2: - 2 ^ 26 < Znth j a 0 < 2 ^ 26) by solve_bounds_by_values_Znth.
  all: try assert(HZnthb1: - 2 ^ 26 < Znth i b 0 < 2 ^ 26) by solve_bounds_by_values_Znth.
  all: try assert(HZnthb2: - 2 ^ 26 < Znth j b 0 < 2 ^ 26) by solve_bounds_by_values_Znth.
  1,2,3,4,5: try (rewrite (Int64.signed_repr (Znth i a 0)) ; [| solve_bounds_by_values]).
  1,2,3,4,5: try (rewrite (Int64.signed_repr (Znth j b 0)) ; [| solve_bounds_by_values]).
  1,2,3,4,5: try (rewrite (Int64.signed_repr (Znth j a 0)) ; [| solve_bounds_by_values]).
  1,2,3,4,5: try (rewrite (Int64.signed_repr (Znth i b 0)) ; [| solve_bounds_by_values]).
  1,2,5: assert(Hab:= M.bound_iter_M_outer _ _ HZntha1 HZnthb2).
  4: assert(Hab:= M.bound_iter_M_outer _ _ HZntha1 HZntha2).
  5: assert(Hab:= M.bound_iter_M_outer _ _ HZnthb1 HZnthb2).

  all: assert(Forall (fun x : ℤ => 0 <= x <= 0)
  [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) 
  by (repeat (apply list.Forall_cons_2 ; [omega|]); apply list.Forall_nil_2).
  1,2,3: try assert(Houter: Forall (fun x : ℤ => 0 + (i + 1) * min_prod (- 2^26) (2^26) (- 2^26) (2^26) <= x <= 
  0 + (i + 1) * max_prod (- 2^26) (2^26) (- 2^26) (2^26)) (outer_M_fix i j a b
           [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])).
  1,3,5: try eapply outer_M_fix_Zbounds.
  all: try eassumption ; try reflexivity ; try omega.
  4: try assert(Houter: Forall (fun x : ℤ => 0 + (i + 1) * min_prod (- 2^26) (2^26) (- 2^26) (2^26) <= x <= 
  0 + (i + 1) * max_prod (- 2^26) (2^26) (- 2^26) (2^26)) (outer_M_fix i j a a
           [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])).
  4: try eapply outer_M_fix_Zbounds.
  all: try eassumption ; try reflexivity ; try omega.
  5: try assert(Houter: Forall (fun x : ℤ => 0 + (i + 1) * min_prod (- 2^26) (2^26) (- 2^26) (2^26) <= x <= 
  0 + (i + 1) * max_prod (- 2^26) (2^26) (- 2^26) (2^26)) (outer_M_fix i j b b
           [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])).
  5: try eapply outer_M_fix_Zbounds.
  all: try eassumption ; try reflexivity ; try omega.
  1,2,3,4,5: rewrite Zlength_map Zlength_map in H7.
  1,2,3 : assert(HZnth: (i + 1) * min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26) <=
    Znth (i + j) (outer_M_fix i j a b
    [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) 0 <=
    (i + 1) * max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) by solve_bounds_by_values_Znth;
    replace ((i + 1) * min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (- (i + 1) * (2 ^ 52)) in HZnth ;
    [ | change (min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (-2^52) ; ring];
    replace ((i + 1) * max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with ((i + 1) * (2 ^ 52)) in HZnth ;
    [ | change (max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (2^52) ; ring].
  4 : assert(HZnth: (i + 1) * min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26) <=
    Znth (i + j) (outer_M_fix i j a a
    [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) 0 <=
    (i + 1) * max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) by solve_bounds_by_values_Znth;
    replace ((i + 1) * min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (- (i + 1) * (2 ^ 52)) in HZnth ;
    [ | change (min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (-2^52) ; ring];
    replace ((i + 1) * max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with ((i + 1) * (2 ^ 52)) in HZnth ;
    [ | change (max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (2^52) ; ring].
  5 : assert(HZnth: (i + 1) * min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26) <=
    Znth (i + j) (outer_M_fix i j b b
    [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) 0 <=
    (i + 1) * max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) by solve_bounds_by_values_Znth;
    replace ((i + 1) * min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (- (i + 1) * (2 ^ 52)) in HZnth ;
    [ | change (min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (-2^52) ; ring];
    replace ((i + 1) * max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with ((i + 1) * (2 ^ 52)) in HZnth ;
    [ | change (max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)) with (2^52) ; ring].
  1,2,3,4,5: rewrite Int64.signed_repr.
  2,4,6,8,10: eapply (M.bound_iter_M_outer2 i _ H5)in HZnth ; solve_bounds_by_values.
  1,2,3,4,5: split.
  1,3,5,7,9: rewrite Int64.signed_repr.
  2,4,6,8,10,11,12,13,14,15: change (2^52) with (4503599627370496) in Hab ; change (-2^52) with (-4503599627370496) in Hab ;
   solve_bounds_by_values.
  1,2,3,4,5: assert(HboundZnthSum := M.bound_iter_M_outer3 i _ _ H5 HZnth Hab).
  1,2,3,4,5: solve_bounds_by_values.
  all: rewrite M.outer_M_fix_a_b; try assumption;
  unfold nm_overlap_array_sep_3 ; simpl ; entailer!.
  }

  + (* mult_2 loop *)
  assert(Hbounds:= M.outer_M_fix_bounds_26 a b H H0 H1 H2).
  rewrite <- Heqt in Hbounds.
  remember (outer_M_fix 16 0 a b t) as contents_t_M1.
  drop_LOCAL_by_name _i.
  match goal with
    [ |- semax _ (PROPx _ (LOCALx ?l _)) _ _ ] => remember l as L
  end.
  freeze [1] F.
  forward_for_simple_bound 15 (M2_Inv F L v_t contents_t_M1) ; subst L.
  thaw_local.
  entailer!.
  rewrite M2_fix_0; cancel.
  assert(Haux2: exists aux2,  Vlong aux2 = Znth i (map Vlong (map Int64.repr (M2_fix i contents_t_M1))) Vundef).
  (erewrite (Znth_map Int64.zero); try (eexists ; reflexivity) ; rewrite Zlength_map ; orewrite M2_fix_Zlength ; subst ; rewrite outer_M_fix_Zlength ; omega).
  assert(Haux1: exists aux1, Vlong aux1 = Znth (i + 16) (map Vlong (map Int64.repr (M2_fix i contents_t_M1))) Vundef).
  (erewrite (Znth_map Int64.zero) ; try(eexists ; reflexivity); rewrite Zlength_map ; orewrite M2_fix_Zlength; subst ; rewrite outer_M_fix_Zlength ; omega).
  destruct Haux2 as [aux2 Haux2];
  destruct Haux1 as [aux1 Haux1];
  forward ; rewrite <- Haux2 ; [entailer!|];
  forward ; rewrite <- Haux1 ; [entailer!|].
  forward.
  entailer!.
  {
  clean_context_from_VST. clears.
  rewrite map_map in Haux2.
  rewrite map_map in Haux1.
  rewrite Zlength_map Zlength_map in H7.
  rewrite (Znth_map 0) in Haux1 ; [|omega].
  rewrite (Znth_map 0) in Haux2 ; [|omega].
  assert(InjVlong: forall a b, Vlong a = Vlong b -> a = b) by congruence.
  apply InjVlong in Haux1.
  apply InjVlong in Haux2.
  rewrite Haux1.
  rewrite Haux2.
  rewrite mul64_repr.
  assert(Zlength
  (outer_M_fix 16 0 a b
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]) = 31).
  rewrite outer_M_fix_Zlength ; omega.
  assert(16 * - 2^52 <= Znth (i + 16)
        (M2_fix i
           (outer_M_fix 16 0 a b
              [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) 0 <= 16 * 2 ^ 52).
  rewrite -Znth_skipn ; try omega.
  rewrite M2_fix_dropZ ; try omega.
  rewrite Znth_nth ; try omega.
  apply Forall_nth_d.
  compute; go.
  apply Forall_skipn.
  assumption.
  assert(Hisub : 0 <= i) by omega.
  assert(Hisup : i < 16) by omega.
  assert(Hp: exists p, p = (16 * - 2 ^ 52 + 38 * (16 * - 2 ^ 52))) by (eexists ; reflexivity).
  assert(Hq: exists q, q = (16 * 2 ^ 52 + 38 * (16 * 2 ^ 52))) by (eexists ; reflexivity).
  destruct Hp as [p Hp].
  destruct Hq as [q Hq].
  assert(Hfun0: (fun x : ℤ => 16 * - 2 ^ 52 <= x <= 16 * 2 ^ 52) 0) by (compute ; go).
  assert(Hbound':= M2_fix_Zbounds _ _ p q _ i Hisub Hisup Hfun0 Hbounds H6 Hp Hq).
  assert(-2810246167479189504 <= (Znth i
        (M2_fix i
           (outer_M_fix 16 0 a b
              [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0])) 0) <= 2810246167479189504).
  apply Forall_Znth.
  omega.
  eapply list.Forall_impl.
  eauto.
  simpl.
  rewrite Hp Hq => x.
  change (16 * - 2 ^ 52 + 38 * (16 * - 2 ^ 52)) with (-2810246167479189504).
  change (16 * 2 ^ 52 + 38 * (16 * 2 ^ 52)) with (2810246167479189504).
  trivial.
  rewrite Int64.signed_repr.
  2: solve_bounds_by_values.
  change (16 * - 2 ^ 52) with (-72057594037927936) in H8.
  change (16 * 2 ^ 52) with (72057594037927936) in H8.
  rewrite Int64.signed_repr.
  rewrite Int64.signed_repr.
  2: solve_bounds_by_values.
  split.
  all: solve_bounds_by_values.
  }
  entailer!.
  rewrite <- M2_fix_step ; try (rewrite outer_M_fix_length ; simpl) ; try omega;
  rewrite M.M2_equiv ; go.

  thaw F.
  (* mult 3 *)
  remember (M2_fix 15 contents_t_M1) as contents_t_M2.
  assert(Zlength contents_t_M1 = 31) by (rewrite Heqcontents_t_M1 ; rewrite outer_M_fix_Zlength ; go).
  assert(Zlength contents_t_M1 = Zlength contents_t_M2) by (subst ; orewrite M2_fix_Zlength ; reflexivity).
  rewrite H5 in H6.
  assert(HM2 := M.M2_fix_bounds contents_t_M1 H5 Hbounds).
  assert(Haux: forall i, 0 <= i < 16 -> exists aux, Vlong aux = Znth (i) (mVI64 contents_t_M2) Vundef) 
  by (intros; erewrite (Znth_map Int64.zero) by (rewrite Zlength_map ; omega) ; eexists ; reflexivity).
  assert(Forall (fun x : ℤ => 39 * 16 * - 2 ^ 52 <= x <= 39 * 16 * 2 ^ 52) (mult_3 contents_t_M2)).
    apply mult_3_bound_le ; go.
  assert(-2^62 < 39 * 16 * - 2 ^ 52) by reflexivity.
  assert(39 * 16 * 2 ^ 52 < 2^62) by reflexivity.
  assert(- 2^62 < 38 * - 2 ^ 47) by reflexivity.
  assert( 2 ^ 16 + 38 * 2 ^ 47 < 2^62) by reflexivity.
  assert(Datatypes.length (mult_3 contents_t_M2) = 16%nat)
   by (unfold mult_3 ; rewrite firstn_length ; rewrite Zlength_correct in H6 ; apply Min.min_l ; omega).
  assert(Zlength (mult_3 contents_t_M2) = 16) by (rewrite Zlength_correct  ; omega).
  assert(HboundM : Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) (mult_3 (M2_fix 15 (M1_fix a b)))).
  {
    unfold M1_fix ; subst.
    eapply list.Forall_impl ; eauto.
    change (39 * 16 * - 2 ^ 52) with (-2810246167479189504).
    change (39 * 16 * 2 ^ 52) with 2810246167479189504.
    intros x0 Hx0 ; simpl in Hx0; 
    solve_bounds_by_values.
  }

  forward_for_simple_bound 16 (M3_Inv sho sha shb v_o v_a v_b v_t o a b contents_t_M2 k).
  unfold nm_overlap_array_sep_3, nm_overlap_array_sep_3' ; entailer!.
  rewrite M3_fix_equation.
  destruct (0 <=? 0) eqn:H000 ; [|tryfalse].
  flatten ; entailer!.
  rename H14 into Hi.
  destruct (Haux i Hi) as [aux HHaux].
  forward ; rewrite -HHaux.
  entailer!.
  1:{
  unfold nm_overlap_array_sep_3' ; flatten.
  all: repeat flatten_sepcon_in_SEP.
  all: forward.
  all: rewrite HHaux;
  rewrite M.M3_equiv;
  repeat match goal with
    | [ |- ENTAIL _, _ |-- _ ] => unfold_entail
    | _ => go
  end.
  }

  remember(M3_fix val 16 (mVI64 contents_t_M2) o) as contents_t_M3.
  rewrite map_map in Heqcontents_t_M3.
  rewrite M3_fix_eq_M3Z in Heqcontents_t_M3 ; try omega.
  rewrite -map_map in Heqcontents_t_M3.
  Intros.
  subst contents_t_M3.

  unfold nm_overlap_array_sep_3' ; flatten.
  all: repeat flatten_sepcon_in_SEP.
  1: freeze [0;2] F.
  2: freeze [0;2] F.
  3: freeze [0;2] F.
  4: freeze [0] F.
  5: freeze [0;2;3] F.

  all: forward_call (v_o,sho,(mult_3 contents_t_M2)).
  1,3,5,7,9: split ; [assumption| split ; try apply car25519_Zlength ; auto]; 
  eapply list.Forall_impl ; eauto; intros ; simpl in *; omega.
  all: forward_call (v_o,sho,car25519 (mult_3 contents_t_M2)).
  all : assert(forall x : ℤ, (fun x0 : ℤ => 38 * - 2 ^ 47 <= x0 < 2 ^ 16 + 38 * 2 ^ 47) x -> - 2 ^ 62 < x < 2 ^ 62) by
  (intros; omega).
  1,3,5,7,9: split ; [assumption|] ; split ; [|rewrite car25519_Zlength ; auto];
      eapply list.Forall_impl; eauto ; intros; omega.
  all: thaw F.

  all: unfold POSTCONDITION.
  all: unfold abbreviate.
  all: eapply (semax_return_None _ _ _ _ _ (stackframe_of f_M) [Tsh [{v_t}]<<( tarray tlg 31 )-- undef31]).
  all: try reflexivity.
  all: try apply return_outer_gen_refl.
  all: try apply return_inner_gen_canon_nil.
  all: try (eapply canonicalize_stackframe ; [ reflexivity| ]).
  all: try (apply Forall2_cons; [apply fn_data_at_intro ; reflexivity |  apply Forall2_nil]).
  all: match goal with | [ |- context[[?A] ++ [?B]] ] => change ([A] ++ [B]) with ([A ; B]) end.
  all: rewrite /nm_overlap_array_sep_3'.
  all: repeat match goal with 
  | [ H : (_ =? _ ) = true |- _ ] => rewrite H
  | [ H : (_ =? _ ) = false |- _ ] => rewrite H
  end.
  all: assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) (Low.M a b)) by (apply M_bound_Zlength ; assumption).
  all: replace (car25519 (car25519 (mult_3 contents_t_M2))) with (Low.M a b).
  1,3,5,7,9: entailer!.
  all: subst contents_t_M2 contents_t_M1 t.
  all: reflexivity.
Qed.

Close Scope Z.