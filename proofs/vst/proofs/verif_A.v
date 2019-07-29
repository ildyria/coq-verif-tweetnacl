Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_A.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.A.

Open Scope Z.

Definition Gprog : funspecs :=
      ltac:(with_library prog [A_spec]).

Import Low.

Lemma body_A: semax_body Vprog Gprog f_A A_spec.
Proof.
start_function.
unfold nm_overlap_array_sep_3, nm_overlap_array_sep_3' in *.
assert(HA: Zlength (A a b) = 16). rewrite A_Zlength ; omega.
assert(HmA: Zlength (mVI64 (A a b)) = 16). rewrite ?Zlength_map //.
assert(Forall (fun x : ℤ => amin + bmin < x < amax + bmax) (A a b)).  apply A_bound_Zlength_lt ; trivial ; omega.
assert(Htkdp: tkdp 16 (mVI64 (A a b)) o = mVI64 (A a b)). rewrite -HmA tkdp_all ; trivial ; rewrite ?Zlength_map; omega.
assert(Haux1: forall i, 0 <= i < 16 -> exists aux1, Vlong aux1 = Znth i (mVI64 a) Vundef). intros; erewrite (Znth_map Int64.zero) ; [eexists ; reflexivity | rewrite Zlength_map; omega].
assert(Haux2: forall i, 0 <= i < 16 -> exists aux2, Vlong aux2 = Znth i (mVI64 b) Vundef). intros; erewrite (Znth_map Int64.zero) ; [eexists ; reflexivity | rewrite Zlength_map; omega].
assert(Haux3: forall i, 0 <= i < 16 -> exists aux3, Vlong aux3 = Znth i (tkdp i (mVI64 (A a b)) (mVI64 a)) Vundef).
  intros ; rewrite /tkdp -?map_firstn -?map_skipn -?map_app ;
  erewrite (Znth_map Int64.zero);[eexists ; reflexivity | rewrite ?Zlength_map];
  change (firstn (nat_of_Z i) (A a b) ++ skipn (nat_of_Z i) a) with (tkdp i (A a b) a);
  rewrite tkdp_Zlength HA ; omega.
assert(Haux4: forall i, 0 <= i < 16 -> exists aux4, Vlong aux4 = Znth i (tkdp i (mVI64 (A a b)) (mVI64 b)) Vundef).
  intros ; rewrite /tkdp -?map_firstn -?map_skipn -?map_app ;
  erewrite (Znth_map Int64.zero);[eexists ; reflexivity | rewrite ?Zlength_map];
  change (firstn (nat_of_Z i) (A a b) ++ skipn (nat_of_Z i) a) with (tkdp i (A a b) a);
  rewrite tkdp_Zlength HA ; omega.

flatten ; Intros.
1: subst o v_a.
2: subst o v_b.
3: subst b v_b.
4: subst o a v_o v_a.

1: forward_for_simple_bound 16 (A_Inv sho sha shb v_o v_o v_b (mVI64 a) a amin amax b bmin bmax 0);
[ unfold nm_overlap_array_sep_3' ; entailer!| |
  rewrite Htkdp; forward; unfold nm_overlap_array_sep_3' ; entailer!].
2: forward_for_simple_bound 16 (A_Inv sho sha shb v_o v_a v_o (mVI64 b) a amin amax b bmin bmax 1);
[ unfold nm_overlap_array_sep_3' ; entailer! | |
  rewrite Htkdp; forward; unfold nm_overlap_array_sep_3' ; entailer!].
3: forward_for_simple_bound 16 (A_Inv sho sha shb v_o v_a v_a o a amin amax a amin amax 2);
[ unfold nm_overlap_array_sep_3' ; entailer!| |
  rewrite Htkdp; forward; unfold nm_overlap_array_sep_3' ; entailer!].
4: forward_for_simple_bound 16 (A_Inv sho sha shb v_b v_b v_b (mVI64 b) b bmin bmax b bmin bmax 3);
[ unfold nm_overlap_array_sep_3' ; entailer!| |
  rewrite Htkdp; forward; unfold nm_overlap_array_sep_3' ; entailer!].
5: forward_for_simple_bound 16 (A_Inv sho sha shb v_o v_a v_b o a amin amax b bmin bmax 4);
[ unfold nm_overlap_array_sep_3' ; entailer!| |
  rewrite Htkdp; forward; unfold nm_overlap_array_sep_3' ; entailer!].
all: unfold nm_overlap_array_sep_3' ; simpl ; Intros.
all: specialize Haux1 with i ; destruct (Haux1 H7) as [aux1 HHaux1].
all: specialize Haux2 with i ; destruct (Haux2 H7) as [aux2 HHaux2].
all: specialize Haux3 with i ; destruct (Haux3 H7) as [aux3 HHaux3].
all: specialize Haux4 with i ; destruct (Haux4 H7) as [aux4 HHaux4].
all: forward.
3,4,5,6,9,10: rewrite -HHaux1.
1,2,9,10: rewrite -HHaux3.
1,3,5,7,9: entailer!.
all: forward.
7,8: rewrite -HHaux1.
1,2,9,10: rewrite -HHaux2.
5,6: rewrite -HHaux3.
7,8: rewrite -HHaux4.
1,3,5,7,9: entailer!.
all: forward.
all: entailer!.
all: rewrite map_map in HHaux1.
all: rewrite map_map in HHaux2.
all: rewrite (Znth_map 0) in HHaux1; [ | omega ].
all: rewrite (Znth_map 0) in HHaux2; [ | omega ].
all: rewrite Znth_tkdp in HHaux3 ; [ | omega].
all: rewrite Znth_tkdp in HHaux4 ; [ | omega].
all: rewrite map_map in HHaux4.
all: rewrite map_map in HHaux3.
all: try (rewrite (Znth_map 0) in HHaux3; [ | omega ]).
all: try (rewrite (Znth_map 0) in HHaux4; [ | omega ]).
1,3,5,7,9: inversion HHaux1.
1,2,3,4,5: inversion HHaux2.
1,2,3,4,5: inversion HHaux3.
1,2,3,4,5: inversion HHaux4.
all: try assert(-2^62 < (Znth i a 0) < 2 ^ 62) by (solve_bounds_by_values_ H).
all: try assert(-2^62 < (Znth i b 0) < 2 ^ 62) by (solve_bounds_by_values_ H0).
all: try assert((-2^62) + (-2^62) <= Znth i a 0 + Znth i b 0 <= 2^62 + 2^62) by omega.
all: try assert((-2^62) + (-2^62) <= Znth i a 0 + Znth i a 0 <= 2^62 + 2^62) by omega.
all: try assert((-2^62) + (-2^62) <= Znth i b 0 + Znth i b 0 <= 2^62 + 2^62) by omega.
1,2,3,4,5: rewrite ?Int64.signed_repr ; solve_bounds_by_values.
all: unfold nm_overlap_array_sep_3' ; simpl ; data_atify ; cancel ; replace_cancel.
all: unfold A.
  (* postcond |-- loop invariant *)
all: clean_context_from_VST.
all: rewrite /tkdp -?map_firstn -?map_skipn -?map_app in HHaux3.
all: rewrite /tkdp -?map_firstn -?map_skipn -?map_app in HHaux4.
all: inv HHaux1 ; inv HHaux2 ; inv HHaux3 ; inv HHaux4.
(* all: rewrite ?(Znth_map 0) ?take_drop_Zlength ; try omega. *)
all: rewrite add64_repr /nat_of_Z.
(* all: rewrite ?app_Znth2. *)
(* all: try replace (Zlength (firstn (Z.to_nat i) (A _ _))) with i. *)
(* all: rewrite ?Znth_skipn. *)
(* all: rewrite ?Zlength_firstn ?HA. *)
(* all: rewrite ?Z.max_r ?Z.min_l ; try omega. *)
(* all: replace (i - i + i) with i by omega. *)
all: rewrite ?Znth_nth; try omega.
all: rewrite <- ZsubList_nth_Zlength ; try omega.
all: rewrite /tkdp ?simple_S_i ; try omega.
all: rewrite /A in HA, HmA.
all: rewrite (upd_Znth_app_step_Zlength _ _ _ Vundef); try omega.
all: f_equal ; rewrite map_map (Znth_map 0) ?Znth_nth ; try reflexivity.
all: omega.
Qed.


Close Scope Z.