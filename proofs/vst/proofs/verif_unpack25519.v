Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Low.Unpack25519.
Require Import Tweetnacl.Mid.ScalarMult.
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_unpack25519.

(*
sv unpack25519(gf o, const u8 *n)
{
  int i;
  FOR(i,16) o[i]=n[2*i]+((i64)n[2*i+1]<<8);
  o[15]&= (i64) 0x7fff;
}
*)

Open Scope Z.

Definition Gprog : funspecs :=
      ltac:(with_library prog [unpack25519_spec]).

Lemma body_unpack25519: semax_body Vprog Gprog f_unpack25519 unpack25519_spec.
Proof.
start_function.
unfold Sfor.
forward_for_simple_bound 16 (unpack25519_Inv sh tsh o n contents_o contents_n).
entailer!.
forward.
entailer!.
solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
forward.
entailer!.
solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
forward.
entailer!.
replace_cancel.
clean_context_from_VST.
assert(0 <= i) by omega.
assert(i < 16) by omega.
rewrite ?map_firstn.

rewrite Int.unsigned_repr.
2: solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
rewrite Int.unsigned_repr.
2: solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
rewrite Int.unsigned_repr.
2: solve_bounds_by_values.
rewrite Int64.shl_mul_two_p.
rewrite Int64.unsigned_repr.
2: solve_bounds_by_values.
rewrite mul64_repr.
rewrite add64_repr.
orewrite Znth_nth.

orewrite Znth_nth.
replace (nat_of_Z (2 * i))%nat with (2 * nat_of_Z i)%nat.
2: rewrite /nat_of_Z Z2Nat.inj_mul //.

replace (nat_of_Z (2 * i + 1))%nat with (2 * nat_of_Z i + 1)%nat.
2:{
rewrite /nat_of_Z.
orewrite Z2Nat.inj_add.
orewrite Z2Nat.inj_mul => //.
}

rewrite Z.mul_comm.
replace (two_p 8) with (Z.pow 2 8) by reflexivity.
rewrite -unpack_for_nth simple_S_i //.
assert(Hval: exists d, d= Vundef).
eexists ; reflexivity.
destruct Hval as [d Hd].

assert(Hzero: exists d, d= Int64.zero).
eexists ; reflexivity.
destruct Hzero as [z Hzero].

rewrite (upd_Znth_app_step_Zlength _ _ _ d) ; try omega.

f_equal.
rewrite (Znth_map z).
f_equal.
erewrite Znth_map.
f_equal.
erewrite Znth_nth => //.
rewrite Unpack_for_Zlength_16_32 //.
rewrite Zlength_map Unpack_for_Zlength_16_32 //.
rewrite ?Zlength_map Unpack_for_Zlength_16_32 //.

rewrite list.drop_ge.
rewrite app_nil_r.
rewrite list.take_ge.

2:{
unfold nat_of_Z.
move: H0 H1 ; rewrite ?Zlength_correct => H0 H1.
rewrite (Unpack_for_length 8 _ _ 32%nat) ; go.
}

2:{
rewrite Zlength_correct in H1.
assert(Datatypes.length contents_o = 16%nat) by omega.
by rewrite H2.
}

assert(Haux: exists aux, Vlong aux = (Znth 15
     (map Vlong
        (map Int64.repr (unpack_for 8 contents_n)))
     Vundef)).
{
  eexists. rewrite (Znth_map Int64.zero) //.
  rewrite Zlength_map Unpack_for_Zlength_16_32 ; omega.
}

destruct Haux as [o15 Ho15].

forward; rewrite -Ho15. (* t <- o[15] *)
entailer!.
forward.
forward.
entailer!.
by apply Unpack25519_bounded.
unfold data_at.
replace_cancel.
clean_context_from_VST.
rewrite upd_Znth_map.
f_equal.
move: Ho15 ; rewrite (Znth_map Int64.zero). rewrite (Znth_map 0). move => Ho15.
2: rewrite Unpack_for_Zlength_16_32 ; omega.
2: rewrite Zlength_map Unpack_for_Zlength_16_32 ; omega.
inversion Ho15.
rewrite and64_repr.
rewrite upd_Znth_map.
f_equal.
unfold Unpack25519.
rewrite upd_Znth_upd_nth ; try omega.
f_equal.
Qed.