Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.Car25519.
Require Import Tweetnacl.Low.Car25519_bounds.
Require Import Tweetnacl.Low.Carry_n.
Require Import Tweetnacl.Low.BackCarry.
Require Import Tweetnacl_verif.spec_car25519.
Require Import Tweetnacl_verif.verif_car25519_compute.

Open Scope Z.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
      ltac:(with_library prog [car25519_spec]).

Lemma body_car25519: semax_body Vprog Gprog f_car25519 car25519_spec.
Proof.
start_function.
unfold Sfor.
forward_for_simple_bound 15 (car25519_Inv sh v_o o).
- entailer!.
  flatten ; entailer!.
- assert(0 <= i < Zlength (Carrying_n 16 (nat_of_Z i) 0 o)).
  {
    rewrite Carrying_n_Zlength.
    go.
    rewrite -Zlength_correct.
    rewrite /nat_of_Z Z2Nat.id ; omega.
  }
  assert(0 <= i + 1 < Zlength (Carrying_n 16 (nat_of_Z i) 0 o)).
  {
    rewrite Carrying_n_Zlength.
    go.
    rewrite -Zlength_correct.
    rewrite /nat_of_Z Z2Nat.id ; omega.
  }
  assert(Hc: exists c, Vlong c = Znth i (map Vlong (map Int64.repr (Carrying_n 16 (nat_of_Z i) 0 o)))
        Vundef).
  { 
    erewrite (Znth_map Int64.zero).
    eexists ; reflexivity.
    rewrite Zlength_map ; go.
  }
  destruct Hc as [c Hc].
  assert(Hd: exists d, Vlong d = Znth (i + 1) (map Vlong (map Int64.repr (Carrying_n 16 (nat_of_Z i) 0 o)))
        Vundef).
  {
    erewrite (Znth_map Int64.zero).
    go.
    rewrite Zlength_map ; go.
  }
  destruct Hd as [d Hd].
  assert(Him: 0 <= i < 16) by omega.
  assert(Hlengtho: length o = 16%nat).
    rewrite Zlength_correct in H0 ; omega.
  assert(Hcb:= Zcarry_n_bounds_length o Hlengtho H i Him).
  assert(Hi1m: 0 <= i + 1 < 16) by omega.
  assert(Hdb:= Zcarry_n_bounds_length o Hlengtho H (i + 1) Hi1m).
  forward ; rewrite <- Hd.
  entailer!.
  forward ; rewrite <- Hc.
  entailer!.
  rewrite map_map in Hd.
  rewrite (Znth_map 0) in Hd.
  2: omega.
  inversion Hd.
  clear Hd.
  rename H6 into Hd.
  rewrite map_map (Znth_map 0) in Hc.
  2: omega.
  inversion Hc.
  clear Hc.
  rename H6 into Hc.
  assert(- 2 ^ 62 < (Znth (i + 1) (Carrying_n 16 (nat_of_Z i) 0 o) 0) < 2 ^ 62).
  rewrite Znth_nth /nat_of_Z; try omega.
  rewrite Carrying_n_1 ; try omega.
  rewrite -Znth_nth ; try omega.
  solve_bounds_by_values_Znth.
  assert(- 2 ^ 63 < Znth i (Carrying_n 16 (nat_of_Z i) 0 o) 0 < 2 ^ 63) by solve_bounds_by_values_Znth.
  assert(-9223372036854775807 <= Znth i (Carrying_n 16 (nat_of_Z i) 0 o) 0 <= 9223372036854775807).
  solve_bounds_by_values.
  assert(- 9223372036854775807 / 65536 <= Znth i (Carrying_n 16 (nat_of_Z i) 0 o) 0 / 65536 <= 9223372036854775807 / 65536).
  apply div_interval_mono.
  compute ; reflexivity.
  omega.
  change (-9223372036854775807 / 65536) with (-140737488355328) in H8.
  change (9223372036854775807 / 65536) with (140737488355327) in H8.
  forward.
  entailer!.
  {
  rewrite Int64.signed_repr.
  rewrite Int64.shr_div_two_p.
  change (two_p 16) with 65536.
  rewrite (Int64.signed_repr (Znth i (Carrying_n 16 (nat_of_Z i) 0 o) 0)).
  rewrite Int64.unsigned_repr.
  rewrite Int64.signed_repr.
  all: solve_bounds_by_values.
  }
  forward.
  entailer!.
  {
  clean_context_from_VST.
  rewrite upd_Znth_diff;
  rewrite ?(Znth_map Int64.zero); rewrite ?Zlength_map ; go.
  }
  forward.
  entailer!.
  {
  replace_cancel.
  clean_context_from_VST.
  apply car_low_level; try assumption.
  rewrite Zlength_map ; assumption.
  }
  (* THIS IS AN IMPORTANT PROOF *)
  Opaque Carrying_n.
  assert(HZl: Zlength (Carrying_n 16 15 0 o) = 16).
    rewrite Carrying_n_Zlength ; [ |rewrite Zlength_correct in H0] ; go.
  assert(Hc: exists c, Vlong c = Znth 15 (map Vlong (map Int64.repr (Carrying_n 16 (nat_of_Z 15) 0 o)))
        Vundef).
  {
    erewrite (Znth_map Int64.zero). go.
    rewrite Zlength_map; rewrite Carrying_n_Zlength ; [ |rewrite Zlength_correct in H0] ; go.
  }
  destruct Hc as [c Hc].
  assert(Hd: exists d, Vlong d = Znth 0 (map Vlong (map Int64.repr (Carrying_n 16 (nat_of_Z 15) 0 o)))
        Vundef).
  {
    erewrite (Znth_map Int64.zero). go.
    rewrite Zlength_map ; rewrite Carrying_n_Zlength ; [ |rewrite Zlength_correct in H0] ; go.
  }
  assert(Him: 0 <= 15 < 16) by omega.
  assert(Hlengtho: length o = 16%nat).
    rewrite Zlength_correct in H0 ; omega.
  assert(Hcb:= Zcarry_n_bounds_length o Hlengtho H 15 Him).
  destruct Hd as [d Hd].
  forward ; rewrite <- Hd.
  entailer!.
  forward ; rewrite <- Hc.
  entailer!.
  change (Pos.to_nat 15) with (15%nat) in *.
  change (nat_of_Z 15) with (15%nat) in *.
  change (Z.to_nat 15) with (15%nat) in *.
  rewrite map_map in Hc.
  rewrite map_map in Hd.
  rewrite (Znth_map 0) in Hc.
  2: omega.
  rewrite (Znth_map 0) in Hd.
  2: omega.
  inv Hd.
  inv Hc.
  assert(- 2 ^ 63 < Znth 15 (Carrying_n 16 15 0 o) 0 < 2 ^ 63) by solve_bounds_by_values_Znth.
  assert(-9223372036854775807 <= Znth 15 (Carrying_n 16 15 0 o) 0 <= 9223372036854775807) by solve_bounds_by_values.
  assert(- 9223372036854775807 / 65536 <= Znth 15 (Carrying_n 16 15 0 o) 0 / 65536 <= 9223372036854775807 / 65536).
  apply div_interval_mono. compute ; reflexivity. omega.
  change (-9223372036854775807 / 65536) with (-140737488355328) in H4.
  change (9223372036854775807 / 65536) with (140737488355327) in H4.
  forward.
  entailer!.
  {
  assert(0 <= Znth 0 (Carrying_n 16 15 0 o) 0 < 2^16).
  {
    Transparent Carrying_n.
    destruct o.
    compute ; tryfalse.
    rewrite Carry_n_step.
    rewrite Znth_0_cons.
    apply Reduce.getResidue_bounds.
    omega.
  }
  Opaque Carrying_n.

  rewrite Int64.shr_div_two_p.
  rewrite Int64.unsigned_repr.
  change (two_p 16) with 65536.
  rewrite (Int64.signed_repr (Znth 15 (Carrying_n 16 15 0 o) 0)).
  rewrite mul64_repr.
  rewrite Int64.signed_repr.
  rewrite Int64.signed_repr.
  rewrite Int64.signed_repr.
  split.
  assert(38 * -140737488355328 <= 38 * (Znth 15 (Carrying_n 16 15 0 o) 0 / 65536) <= 38 * 140737488355327).
  apply Mult_interval_correct_pos_le ; omega.
  change (38 * -140737488355328) with (-5348024557502464) in H9.
  change (38 * 140737488355327) with 5348024557502426 in H9.
  all: solve_bounds_by_values.
  }
  forward.
  rewrite upd_Znth_map.
  rewrite (Znth_map Int64.zero).
  2: rewrite upd_Znth_Zlength Zlength_map ; omega.
  entailer!.
  forward.
  forward.
  entailer!.
  apply Zcar25519_bounds_length_1.
  rewrite Zlength_correct in H0; omega.
  auto.
  replace_cancel.
  apply car25519low_level ; trivial.
Qed.


Close Scope Z.