Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.Car25519.
Require Import Tweetnacl.Low.Carry_n.
Require Import Tweetnacl.Low.BackCarry.
Require Import Tweetnacl.Mid.Car25519.
Require Import Tweetnacl.Mid.Reduce.
Local Open Scope Z.

Lemma car_low_level: forall contents_o,
  Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) contents_o ->
  Zlength contents_o = 16 -> forall i, 0 <= i < 15 -> 0 <= i < Zlength (map Int64.repr (Carrying_n 16 (nat_of_Z i) 0 contents_o)) ->
mVI64 (Carrying_n 16 (nat_of_Z (i + 1)) 0 contents_o) =
upd_Znth i
  (upd_Znth (i + 1) (mVI64 (Carrying_n 16 (nat_of_Z i) 0 contents_o))
     (Vlong
        (Int64.add (Int64.repr (Znth (i + 1) (Carrying_n 16 (nat_of_Z i) 0 contents_o) 0))
           (Int64.shr (Int64.repr (Znth i (Carrying_n 16 (nat_of_Z i) 0 contents_o) 0)) (Int64.repr 16)))))
  (force_val
     (sem_cast_l2l
        (force_val
           (sem_and tlg tint
              (Znth i
                 (upd_Znth (i + 1) (mVI64 (Carrying_n 16 (nat_of_Z i) 0 contents_o))
                    (Vlong
                       (Int64.add (Int64.repr (Znth (i + 1) (Carrying_n 16 (nat_of_Z i) 0 contents_o) 0))
                          (Int64.shr (Int64.repr (Znth i (Carrying_n 16 (nat_of_Z i) 0 contents_o) 0)) (Int64.repr 16)))))
                 Vundef) (Vint (Int.repr 65535)))))).
Proof.
  intros contents_o Hcontents_o Hlengthcontents_o i Hi HiL.
  assert(Hlength2: 0 <= i + 1 < Zlength (Carrying_n 16 (nat_of_Z i) 0 contents_o)).
  {
    assert(exists i', nat_of_Z i = i') by eauto.
    destruct H as [i' Hi'].
    assert(0 <= Z.of_nat i' < 15).
    rewrite -Hi' /nat_of_Z Z2Nat.id ; omega.
    rewrite Carrying_n_Zlength ; [ |rewrite Zlength_correct in Hlengthcontents_o] ; go.
  }
  rewrite upd_Znth_map.
  repeat rewrite Int64.shr_div_two_p.
  rewrite (Int64.unsigned_repr 16).
  2: solve_bounds_by_values.
  rewrite add64_repr.
  rewrite upd_Znth_map.
  rewrite (Znth_map Int64.zero).
  2: rewrite Zlength_map upd_Znth_Zlength ; omega.
  rewrite (Znth_map 0).
  2: rewrite upd_Znth_Zlength ; omega.
  rewrite (Int64.signed_repr (Znth i (Carrying_n 16 (nat_of_Z i) 0 contents_o) 0)).
  2: {
  apply Forall_Znth ; try omega.
  eapply list.Forall_impl.
  rewrite Zlength_correct in Hlengthcontents_o;
  eapply Zcarry_n_bounds_length ; go.
  intros ; simpl in H ; solve_bounds_by_values.
  }
  rewrite /sem_and /tint /sem_binarith /classify_binarith.
  simpl sem_cast.
  rewrite /sem_cast_i2l /sem_cast_l2l /both_long /force_val.
  rewrite /cast_int_long.
  rewrite and64_repr.
  rewrite upd_Znth_map.
  rewrite upd_Znth_map.
  f_equal.
  f_equal.
  rewrite Int.signed_repr.
  2: solve_bounds_by_values.
  change 65535 with (Z.ones 16).
  rewrite Z.land_comm.
  repeat orewrite upd_Znth_upd_nth.
  repeat orewrite Znth_nth.
  unfold nat_of_Z.
  assert(Hi': exists i', Z.to_nat i = i') by eauto.
  destruct Hi' as [i' Hi'].
  assert_gen_hyp_ Hid i 14 14.
  omega.
  rewrite Zlength_correct in Hlengthcontents_o.
  assert(Ho' : (length contents_o = 16)%nat) by go.
  repeat (destruct contents_o ; tryfalse).

  repeat match goal with
      | [H : _ \/ _ |- _ ] => destruct H ; subst
      | _ => idtac
    end; Grind_add_Z; repeat change_Z_to_nat ; repeat rewrite Carry_n_step ; repeat rewrite Carry_n_step_0 ; unfold upd_nth ; unfold nth;
  unfold getResidue ;
  unfold getCarry ;
  repeat orewrite Int64.Zshiftl_mul_two_p ; repeat orewrite Int64.Zshiftr_div_two_p ; reflexivity.
Qed.

Lemma car25519low_level: forall o, Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) o ->
Zlength o = 16 ->
forall c, Vlong c = Vlong (Int64.repr (Znth 15 (Carrying_n 16 15 0 o) 0)) ->
forall d, Vlong d = Vlong (Int64.repr (Znth 0 (Carrying_n 16 15 0 o) 0)) ->
mVI64 (car25519 o) =
upd_Znth 15
  (upd_Znth 0 (mVI64 (Carrying_n 16 (Pos.to_nat 15) 0 o))
     (Vlong (Int64.add d (Int64.mul (Int64.repr 38) (Int64.shr c (Int64.repr 16))))))
  (force_val
     (sem_cast_l2l
        (force_val
           (sem_and tlg tint
              (Znth 15
                 (upd_Znth 0 (mVI64 (Carrying_n 16 (Pos.to_nat 15) 0 o))
                    (Vlong (Int64.add d (Int64.mul (Int64.repr 38) (Int64.shr c (Int64.repr 16)))))) Vundef)
              (Vint (Int.repr 65535)))))).
Proof.
  intros o Ho Hlengtho c Hc d Hd.
  assert(HZl: Zlength (Carrying_n 16 15 0 o) = 16).
    rewrite Carrying_n_Zlength ; [omega |rewrite Zlength_correct in Hlengtho] ; rewrite Hlengtho ; compute ; reflexivity.
  change (Pos.to_nat 15) with (15%nat) in *.
  change (nat_of_Z 15) with (15%nat) in *.
  change (Z.to_nat 15) with (15%nat) in *.
  assert(Hlength': Datatypes.length o = 16%nat).
    rewrite Zlength_correct in Hlengtho ; omega.
  assert(Hlength: 0 <= 15 < Zlength (Carrying_n 16 15 0 o)).
    rewrite Carrying_n_Zlength; try omega ; rewrite Hlength'; reflexivity.
  assert(H1516: 0 <= 15 < 16) by omega.
  assert(H016: 0 <= 0 < 16) by omega.
  assert(Hcorrolary15 := Zcarry_n_bounds_length o Hlength' Ho 15 H1516).
  assert(Hcorrolary0 := Zcarry_n_bounds_length o Hlength' Ho 0 H016).
  change (Z.to_nat 15) with 15%nat in Hcorrolary15.
  change (Z.to_nat 0) with 0%nat in Hcorrolary0.
  assert(Vlong_inv: forall a b, Vlong a = Vlong b -> a = b) by congruence.
  apply Vlong_inv in Hc.
  apply Vlong_inv in Hd.
  subst c d.
  repeat rewrite Int64.shr_div_two_p.
  rewrite (Int64.unsigned_repr 16).
  2: solve_bounds_by_values.
  rewrite mul64_repr.
  rewrite add64_repr.
  rewrite upd_Znth_map.
  rewrite (Znth_map Int64.zero).
  2: rewrite upd_Znth_Zlength Zlength_map ; omega.
  rewrite /sem_and /tint /sem_binarith /classify_binarith.
  simpl sem_cast.
  rewrite /sem_cast_i2l /sem_cast_l2l /both_long /force_val /cast_int_long.
  rewrite upd_Znth_map.
  rewrite upd_Znth_map.
  rewrite (Znth_map 0).
  2: rewrite upd_Znth_Zlength ; omega.
  rewrite and64_repr.
  rewrite upd_Znth_map.
  f_equal.
  f_equal.
  unfold car25519.
  remember (Carrying_n 16 15 0 o) as carr_list.
  assert(Hlength_car: (length carr_list = 16)%nat).
    subst ; rewrite Carrying_n_length ; rewrite Zlength_correct in Hlengtho ; omega.
  rewrite Int.signed_repr.
  2: solve_bounds_by_values.
  rewrite Int64.signed_repr.
  2:{
    apply Forall_Znth.
    omega.
    eapply Forall_impl ; eauto;
    let Hx := fresh in intros ? Hx ;
    simpl in Hx;
    solve_bounds_by_values.
  }
  repeat (destruct carr_list ; tryfalse).
  simpl backCarry;
  repeat orewrite upd_Znth_upd_nth;
  repeat orewrite Znth_nth;
  unfold nat_of_Z;
  repeat change_Z_to_nat;
  unfold nth;
  unfold upd_nth;
  unfold getResidue;
  unfold getCarry.
  change 65535 with (Z.ones 16).
  rewrite Z.land_comm.
  orewrite Int64.Zshiftr_div_two_p => //.
Qed.

Close Scope Z.