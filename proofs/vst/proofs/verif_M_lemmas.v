Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl_verif.verif_M_compute.

Open Scope Z.

Module M.

Lemma lemma_t_defined : forall i, 0 <= i < 31 -> map Vlong (list_repeat (Z.to_nat (i + 1)) Int64.zero) ++
list_repeat (Z.to_nat (31 - (i + 1))) Vundef =
upd_Znth i
  (map Vlong (list_repeat (Z.to_nat i) Int64.zero) ++
   list_repeat (Z.to_nat (31 - i)) Vundef) (Vlong (Int64.repr 0)).
Proof.
  intros i Hi.
  rewrite upd_Znth_app2.
  replace (Z.to_nat (i + 1)) with ((Z.to_nat i + 1)%nat).
  rewrite <- list_repeat_app.
  simpl.
  rewrite map_app.
  rewrite app_assoc_reverse.
  rewrite Zlength_map.
  rewrite Zlength_list_repeat; try omega.
  simpl.
  replace (list_repeat (Z.to_nat (31 - i)) Vundef) with ([Vundef] ++ list_repeat (Z.to_nat (31 - (i + 1))) Vundef).
  replace (i - i) with 0 by omega.
  rewrite upd_Znth_app1 ; go.

  replace (Z.to_nat (31 - i)) with ((1 + Z.to_nat (31 - (i + 1)))%nat).
  rewrite <- list_repeat_app ; auto.

  rewrite Z.sub_add_distr.
  replace (1 + Z.to_nat (31 - i - 1))%nat with (Z.to_nat (1 + 31 - i - 1)).
  f_equal ; omega.

  change (1 + Z.to_nat (31 - i - 1))%nat with (Z.to_nat 1 + Z.to_nat (31 - i - 1))%nat.
  rewrite <- Z2Nat.inj_add by omega.
  rewrite Z2Nat.inj_iff ; omega.

  change (Z.to_nat i + 1)%nat with (Z.to_nat i + Z.to_nat 1)%nat.
  rewrite <- Z2Nat.inj_add by omega ; omega.

  rewrite Zlength_map.
  rewrite Zlength_list_repeat; try omega.
  inequality_sum_Zlength.
Qed.

Lemma t_31_0 : map Vlong (list_repeat (Z.to_nat 31) Int64.zero) ++ list_repeat (Z.to_nat (31 - 31)) Vundef =
 map Vlong (map Int64.repr [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]).
Proof. reflexivity. Qed.

Lemma outer_M_fix_a_b: forall i j aux aux1 aux2 (contents_a contents_b: list Z),
0 <= i < 16 ->
0 <= j < 16 ->
Zlength contents_a = 16 ->
Zlength contents_b = 16 ->
Zlength [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0] = 31 ->
Vlong aux1 = Znth i (map Vlong (map Int64.repr contents_a)) Vundef ->
Vlong aux2 = Znth j (map Vlong (map Int64.repr contents_b)) Vundef ->
Vlong aux = Znth (i + j) (map Vlong (map Int64.repr (outer_M_fix i j contents_a contents_b
[0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))) Vundef
-> 
upd_Znth (i + j)
     (map Vlong
        (map Int64.repr
           (outer_M_fix i j contents_a contents_b
              [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
              0; 0; 0; 0; 0; 0; 0; 0; 0; 0])))
     (Vlong (Int64.add aux (Int64.mul aux1 aux2)))
=
(map Vlong
         (map Int64.repr
            (outer_M_fix i (j + 1) contents_a contents_b
               [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
               0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]))).
Proof.
  intros i j aux aux1 aux2 a b Hi Hj Ha Hb Ht Haux1 Haux2 Haux.
  rewrite upd_Znth_map.
  rewrite (Znth_map Int64.zero) in Haux1. 2: (rewrite Zlength_map ; go).
  rewrite (Znth_map Int64.zero) in Haux2. 2: (rewrite Zlength_map ; go).
  rewrite (Znth_map 0) in Haux1. 2: go.
  rewrite (Znth_map 0) in Haux2. 2: go.
  rewrite (Znth_map Int64.zero) in Haux. 2: (rewrite Zlength_map ; rewrite outer_M_fix_Zlength ; go).
  rewrite (Znth_map 0) in Haux. 2: (rewrite outer_M_fix_Zlength ; go).

  inversion Haux1.
  inversion Haux2.
  inversion Haux.
  rewrite mul64_repr.
  rewrite add64_repr.
  rewrite upd_Znth_map.
  rewrite (outer_M_fix_equation i (j + 1)).
  assert(Hiii: i = 0 \/ 0 < i) by omega.

  destruct Hiii.
  subst ; simpl.
  rewrite outer_M_fix_0'.
  rewrite  (inner_M_fix_equation 0 (j + 1)).
  flatten.
    apply Z.leb_le in Eq ; omega.
  replace (j + 1 - 1) with j by omega.
  change (0 + j) with j.
  f_equal.
  f_equal.
  rewrite inner_M_fix_0 ; go.
  rewrite <- list.nth_lookup.
  rewrite <- Znth_nth ; reflexivity.

  flatten.
    apply Z.leb_le in Eq ; omega.
  rewrite outer_M_fix_i_1 ; go.
Qed.

Lemma outer_M_fix_bounds_26 : 
  forall a b,
  Forall (fun x : ℤ => - 2 ^ 26 < x < 2 ^ 26) a ->
  Forall (fun x : ℤ => - 2 ^ 26 < x < 2 ^ 26) b ->
  Zlength a = 16 ->
  Zlength b = 16 ->
  Forall (fun x : ℤ => 16 * (- 2 ^ 52) <= x <= 16 * 2 ^ 52) (outer_M_fix 16 0 a b [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]).
Proof.
  intros.
  replace (outer_M_fix 16 0 a b
       [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0;
       0; 0; 0; 0; 0; 0; 0]) with (mult_1 a b).
  eapply (mult_1_bound_le a b (-2^26) (2^26) (-2^26) (2^26)) ;
  try apply Forall_bounds_le_lt; 
  rewrite ?H1 ?H2 ; auto ; compute ; split ; intro ; tryfalse.
  rewrite <- M1_fix_eq_M1Z ; auto.
Qed.

Lemma M2_equiv :
  forall i t aux1 aux2,
  0 <= i < 15 ->
  Zlength t = 31 ->
  Vlong aux1 = Znth (i + 16) (map Vlong (map Int64.repr (M2_fix i t))) Vundef ->
  Vlong aux2 = Znth i (map Vlong (map Int64.repr (M2_fix i t))) Vundef ->
  (upd_Znth i (map Vlong (map Int64.repr (M2_fix i t)))
     (Vlong (Int64.add aux2 (Int64.mul (Int64.repr 38) aux1))))
= (map Vlong (map Int64.repr (update_M2_i (Z.to_nat i) (M2_fix i t)))).
Proof.
  intros i t aux1 aux2 Hi Ht Haux1 Haux2.
  rewrite (Znth_map Int64.zero) in Haux1. 2: (rewrite Zlength_map ;rewrite M2_fix_Zlength ; omega).
  rewrite (Znth_map Int64.zero) in Haux2. 2: (rewrite Zlength_map ;rewrite M2_fix_Zlength ; omega).
  rewrite (Znth_map 0) in Haux1. 2: (rewrite M2_fix_Zlength ; omega).
  rewrite (Znth_map 0) in Haux2. 2: (rewrite M2_fix_Zlength ; omega).
  inv Haux1.
  inv Haux2.
  rewrite upd_Znth_map.
  f_equal.
  unfold update_M2_i.
  unfold local_update_M2.
  rewrite mul64_repr.
  rewrite add64_repr.
  rewrite upd_Znth_map.
  rewrite (upd_Znth_alter Z (fun x => (Znth i (M2_fix i t) 0 + 38 * Znth (i + 16) (M2_fix i t) 0))) ; auto.
  rewrite <- list.nth_lookup.
  f_equal.
    remember (M2_fix i t) as ltemp.
    assert(length ltemp = 31%nat).
      rewrite Heqltemp ; rewrite M2_fix_length ; try omega ; rewrite Zlength_correct in Ht; go.
    apply list.list_alter_ext ; try reflexivity.
    intros x Hx.
    apply (list.nth_lookup_Some _ _ 0) in Hx.
    subst x.
    repeat rewrite Znth_nth ; try omega.
    unfold nat_of_Z.
    rewrite Z2Nat.inj_add ; try omega.
    reflexivity.
  omega.
  rewrite M2_fix_Zlength ; omega.
Qed.

Lemma M2_fix_bounds : 
  forall t,
  Zlength t = 31 ->
  Forall (fun x : ℤ => 16 * (- 2 ^ 52) <= x <= 16 * 2 ^ 52) t ->
  Forall (fun x : ℤ => 39 * 16 * (- 2 ^ 52) <= x <= 39 * 16 * 2 ^ 52) (M2_fix 15 t).
Proof.
  intros t Hlt HFt.
  eapply M2_fix_bounds ; eauto.
  omega.
  compute ; split ; intro ; tryfalse.
  rewrite Zlength_correct in Hlt ; go.
Qed.

Lemma M3_equiv : forall i l o,
  0 <= i < 16 ->
  Zlength l = 31 ->
  Zlength o = 16 ->
  upd_Znth i
     (M3_fix val i (mVI64 l) o)
     (Znth i (mVI64 l) Vundef)
  = (M3_fix val (i + 1) (mVI64 l) o).
Proof.
  intros i l o Hi Hl Ho.
  rewrite (Znth_map Int64.zero). 2: (rewrite Zlength_map ; go).
  rewrite (Znth_map 0). 2: omega.
  assert(Hll:= Zlength_correct l).
  assert(Hoo:= Zlength_correct o).
  rewrite -(Znth_map _ _ _ _ _ (Int64.repr 0)).
  2: omega.
  rewrite -(Znth_map _ _ _ _ _ (Vlong (Int64.repr 0))).
  2: rewrite Zlength_map ; omega.
  rewrite (M3_fix_step _ _ _ _ (Vlong (Int64.repr 0))) ; go.
  2: rewrite ?map_length ; omega.
  assert(Zlength (firstn (Z.to_nat i) (M3_fix val i (mVI64 l) o)) = Z.of_nat (Z.to_nat i)).
    rewrite Zlength_firstn.
    rewrite Z.max_r ; try omega.
    rewrite Z.min_l.
    rewrite Z2Nat.id; go.
    rewrite <- M3_fix_Zlength ; omega.
  rewrite <- (firstn_skipn (Z.to_nat i) (M3_fix val i (mVI64 l) o)).
  rewrite upd_Znth_app2.
  2: rewrite H.
  rewrite (firstn_skipn (Z.to_nat i) (M3_fix _ i _ o)).
  rewrite H.
  rewrite (nth_drop _ _ (Vlong (Int64.repr 0))).
  replace (i - Z.of_nat (Z.to_nat i)) with 0.
  2: rewrite Z2Nat.id ; omega.
  rewrite upd_Znth_cons.
  rewrite app_assoc_reverse.
  f_equal.
  rewrite <- app_comm_cons.
  rewrite app_nil_l.
  rewrite Znth_nth.
  f_equal.
  f_equal.
  omega.
  omega.
  rewrite <- (Nat2Z.id (Datatypes.length (M3_fix val i _ o))%nat).
  rewrite <- Z2Nat.inj_lt ; try erewrite <- M3_fix_length ; go.
  rewrite Z2Nat.id ; try omega.
  inequality_sum_Zlength.
Qed.

Lemma bound_iter_M_outer : forall a b,
  - 2 ^ 26 < a < 2 ^ 26 ->
  - 2 ^ 26 < b < 2 ^ 26 ->
  - 2 ^ 52 < a * b < 2 ^ 52.
Proof.
intros.
change (-2^52) with (min_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)).
change (2^52) with (max_prod (- 2 ^ 26) (2 ^ 26) (- 2 ^ 26) (2 ^ 26)).
apply Mult_interval_correct_min_max_lt ; assumption.
Qed.

Lemma bound_iter_M_outer2: forall i a,
  0 <= i < 16 ->
  - (i + 1) * 2 ^ 52 <= a <= (i + 1) * 2 ^ 52 ->
  -72057594037927936 <= a <= 72057594037927936.
Proof.
  intros.
  assert(-16 * 2 ^ 52 <= - (i + 1) * 2 ^ 52).
  apply Zmult_le_compat_r.
  omega.
  go.
  assert((i + 1) * 2 ^ 52 <= 16 * 2 ^ 52).
  apply Zmult_le_compat_r.
  omega.
  go.
  change (16 * 2 ^52) with 72057594037927936 in H2.
  change (-16 * 2 ^52) with (-72057594037927936) in H1.
  omega.
Qed.

Lemma bound_iter_M_outer3: forall i a b,
  0 <= i < 16 ->
  - (i + 1) * 2 ^ 52 <= a <= (i + 1) * 2 ^ 52 ->
  - 2 ^ 52 < b < 2 ^ 52 ->
  - 2 ^ 63 < a + b < 2 ^ 63.
Proof.
  intros.
  apply (bound_iter_M_outer2 _ _ H) in H0.
  change (2^52) with (4503599627370496) in H1.
  change (-2^52) with (-4503599627370496) in H1.
  solve_bounds_by_values.
Qed.

End M.


Close Scope Z.