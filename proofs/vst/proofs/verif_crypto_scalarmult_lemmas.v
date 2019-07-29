Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.missing_lemmae.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.Prep_n.
Require Import Tweetnacl.Low.Pack25519.
Require Import Tweetnacl.Low.Unpack25519.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl.Low.Prep_n.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_rev.
Require Import Tweetnacl.Low.GetBit.
Require Import Tweetnacl.Low.Inv25519.
Require Import Tweetnacl.Low.Constant.
Require Import Tweetnacl.Low.Pack25519.

Local Open Scope Z.

Lemma clamped_n : forall l, Zlength l = 32 ->
        Forall (fun x => 0 <= x < Z.pow 2 8) l ->
        map Vint (map Int.repr (clamp l)) = upd_Znth 0
                 (upd_Znth 31 (map (fun x : ℤ => Vint (Int.repr x)) (firstn 31 l) ++ [Vundef])
                 (Vint (Int.zero_ext 8 (Int.or (Int.and (Int.repr (Znth 31 l 0)) (Int.repr 127)) (Int.repr 64)))))
                 (Vint (cast_int_int I8 Unsigned (Int.and (Int.repr (Znth 0 (firstn 31 l) 0)) (Int.repr 248)))).
Proof.
intros.

assert(0 < Zlength (firstn 31 l)).
change 31%nat with (Z.to_nat 31); rewrite Zlength_firstn ?Z.max_r ?Z.min_l ; omega.

assert(0 < Zlength (map Vint (map Int.repr (firstn 31 l)))).
by rewrite ?Zlength_map.

assert(0 <= 31 < Zlength (map Vint (map Int.repr (firstn 31 l)) ++ [Vundef])).
rewrite Zlength_app ?Zlength_map.
change 31%nat with (Z.to_nat 31).
rewrite Zlength_firstn ?Z.max_r ?Z.min_l ; try omega.
compute ; go.
rewrite upd_Znth_app2.

2: {
rewrite Zlength_map.
change (31%nat) with (Z.to_nat 31).
rewrite Zlength_firstn ?Z.min_l Z.max_r ; try omega.
compute ; go.
}

replace (31 - Zlength (map (fun x : ℤ => Vint (Int.repr x)) (firstn 31 l))) with 0.
rewrite ?upd_Znth_upd_nth ; try omega.

2: {
rewrite Zlength_map.
change (31%nat) with (Z.to_nat 31).
rewrite Zlength_firstn ?Z.min_l Z.max_r ; try omega.
}
rewrite ?Znth_nth; try omega.

(* BUNCH OF ASSERTS FOR LATER PROOFS *)

assert(Z.land (nth (nat_of_Z 0) (firstn 31 l) 0) 248 < two_p 8).
change(two_p 8) with (2^8).
rewrite nth_firstn.
2: compute ; omega.
apply Z.log2_lt_cancel.
assert(Z.log2 (Z.land (nth 0 l 0) 248) <= Z.min (Z.log2 (nth (nat_of_Z 0) l 0)) (Z.log2 248)).
apply Z.log2_land.
apply Forall_nth_d ; go.
eapply list.Forall_impl.
eauto.
intros ; go.
omega.
assert(Z.min (Z.log2 (nth (nat_of_Z 0) l 0)) (Z.log2 248) < Z.log2 (2 ^ 8)).
apply Z.min_lt_iff.
right.
reflexivity.
eapply Z.le_lt_trans ; eauto.

assert(0 <= Z.land (nth (nat_of_Z 0) (firstn 31 l) 0) 248).
rewrite nth_firstn.
2: compute ; omega.
apply Z.land_nonneg.
right; omega.

assert(H': 0 <= nth (nat_of_Z 31) l 0 < 2^8).
rewrite -Znth_nth.
solve_bounds_by_values_ H0.
omega.

assert(Z.lor (Z.land (nth (nat_of_Z 31) l 0) 127) 64 < two_p 8).
change(two_p 8) with (2^8).
apply Z.log2_lt_cancel.
assert(Z.log2 (Z.land (nth (nat_of_Z 31) l 0) 127) <= Z.min (Z.log2 (nth (nat_of_Z 31) l 0)) (Z.log2 127)).
apply Z.log2_land ; omega.
assert( Z.min (Z.log2 (nth (nat_of_Z 31) l 0)) (Z.log2 127) < Z.log2 (2 ^ 8)).
apply Z.min_lt_iff ; go.
rewrite Z.log2_lor ; try omega.
apply Z.max_lub_lt ; go.
apply Z.land_nonneg ; go.

(* END BUNCH OF ASSERTS FOR LATER PROOFS *)

rewrite upd_nth0.
unfold cast_int_int.
rewrite ?and_repr ?or_repr.
rewrite ?zero_ext_inrange.
replace [Vint (Int.repr (Z.lor (Z.land (nth (nat_of_Z 31) l 0) 127) 64))] 
      with (map (fun x : ℤ => Vint (Int.repr x)) [(Z.lor (Z.land (nth (nat_of_Z 31) l 0) 127) 64)]).
2: reflexivity.
rewrite -map_app.
rewrite upd_nth_map.
rewrite map_map.
f_equal.

unfold clamp.
unfold nat_of_Z.
change (Z.to_nat 0) with 0%nat.
f_equal.
change (Z.to_nat 31) with 31%nat.
rewrite Zlength_correct in H.
change 32 with (ℤ.ℕ 32%nat) in H.
apply Nat2Z.inj in H.
do 32 (destruct l as [|? l]; [tryfalse|]).
destruct l ; [|tryfalse].
simpl.
repeat f_equal.
f_equal.
rewrite nth_firstn.
reflexivity.
omega.

rewrite Int.unsigned_repr.
omega.

change Int.max_unsigned with 4294967295.
change (two_p 8) with 256 in *.
omega.

rewrite Int.unsigned_repr.
omega.

assert(0 <= Z.lor (Z.land (nth (nat_of_Z 31) l 0) 127) 64).
apply Z.lor_nonneg ; split ; try apply Z.land_nonneg ; omega.

change Int.max_unsigned with 4294967295.
change (two_p 8) with 256 in *.
omega.
Qed.

Lemma firstn_skipn_upd_Znth_undef32 : forall i contents_n,
0 <= i < 31 ->
Zlength contents_n = 32 ->
Zlength (map Vint (map Int.repr contents_n)) = 32 ->
(firstn (nat_of_Z (i + 1)) (map Vint (map Int.repr contents_n)) ++ skipn (nat_of_Z (i + 1)) undef32 =
upd_Znth i (firstn (nat_of_Z i) (map Vint (map Int.repr contents_n)) ++ skipn (nat_of_Z i) undef32)
  (Vint (Int.repr (Znth i contents_n 0)))).
Proof.
intros.
rewrite ?map_firstn -(Znth_map _ _ _ _ _ Int.zero) -?(Znth_map _ _ _ _ _ Vundef)
-?(upd_Znth_app_step_Zlength i (map Vint (map Int.repr contents_n))); try omega.
f_equal; f_equal; rewrite /nat_of_Z Z2Nat.inj_succ //; omega.
rewrite undef32_Zlength ; omega.
rewrite ?Zlength_map.
rewrite H0; omega.
Qed.

Lemma Zlength_firstn_32_str_pos : forall A (contents_n:list A),
Zlength contents_n = 32 ->
0 < Zlength (firstn 31 contents_n).
Proof.
intros;
change 31%nat with (Z.to_nat 31);
rewrite Zlength_firstn Z.max_r ?Z.min_l ; omega.
Qed.

Lemma isInt8Unsignedcontents_n : forall contents_n,
Zlength contents_n = 32 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 8) contents_n ->
0 < Zlength (firstn 31 contents_n) ->
0 < Zlength (firstn 31 (map Vint (map Int.repr contents_n))) ->
0 <= 31 < Zlength (firstn 31 (map Vint (map Int.repr contents_n)) ++ [Vundef]) ->
31 >= 0 ->
Zlength (map Vint (map Int.repr contents_n)) = 32 ->
  is_int I8 Unsigned
    (Znth 0
       (upd_Znth 31 (firstn 31 (map Vint (map Int.repr contents_n)) ++ [Vundef])
          (Vint (Int.zero_ext 8 (Int.repr (Z.lor (Z.land (Znth 31 contents_n 0) 127) 64))))) Vundef).
Proof.
intros.
replace (Znth 0 (upd_Znth 31 (firstn 31 (map Vint (map Int.repr contents_n)) ++ [Vundef])
        (Vint (Int.zero_ext 8 (Int.repr (Z.lor (Z.land (Znth 31 contents_n 0) 127) 64))))) Vundef) with (Vint (Int.repr (Znth 0 (firstn 31 contents_n) 0))).
simpl.
rewrite Int.unsigned_repr; change 31%nat with (Z.to_nat 31);
rewrite Znth_firstn ; try omega;
solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
rewrite upd_Znth_diff; try omega.
orewrite app_Znth1.
by rewrite -?map_firstn ?map_map ?(Znth_map 0) ; try omega.
Qed.

Lemma i254div8bound : forall i, 0 <= i <= 254 -> 0 <= i / two_p 3 <= 254 / two_p 3.
Proof.
  split;
  repeat match goal with
  | _=> apply Z.div_pos
  | _=> apply Z.div_le_mono
  | _=> reflexivity
  | _=> omega
  end.
Qed.

Lemma Intusignedshr32 : forall i, 0 <= i <= 254 -> 0 <= Int.unsigned (Int.shr (Int.repr i) (Int.repr 3)) < 32.
Proof.
  Opaque two_p.
  intros.
  assert(Hidiv8 := i254div8bound i H).
  rewrite Int.shr_div_two_p.
  change (254 / two_p 3) with 31 in Hidiv8.
  rewrite ?(Int.unsigned_repr 3) ?Int.signed_repr ?Int.unsigned_repr; solve_bounds_by_values.
Qed.

Lemma izland7_bound : forall i, 0 <= i <= 254 -> 0 <= Z.land i 7 < 32.
Proof.
  intros.
  change 7 with (Z.ones 3).
  orewrite Z.land_ones.
  assert(0 <= i mod 2 ^ 3 < 8).
  apply Z_mod_lt ; omega.
  omega.
Qed.

Lemma Intltutrue : forall i, 0 <= i <= 254 -> Int.ltu (Int.repr (Z.land i 7)) Int.iwordsize = true.
Proof.
  intros.
  change (Int.iwordsize) with (Int.repr 32).
  assert(HSumbool: {Int.ltu (Int.repr (Z.land i 7)) (Int.repr 32) = true} + {Int.ltu (Int.repr (Z.land i 7)) (Int.repr 32) = false}).
  apply Sumbool.sumbool_of_bool.
  destruct HSumbool as [Htrue|Hfalse].
  rewrite Htrue.
  simpl ; trivial.
  exfalso.
  apply ltu_repr_false in Hfalse.
  assert(H' := izland7_bound i H) ; omega.
  assert(H' := izland7_bound i H) ; solve_bounds_by_values.
  solve_bounds_by_values.
Qed.

Lemma data_at_sh_if : forall T SH i a b p ,
  (if 254 =? i
   then data_at SH T a p
   else data_at SH T b p)
  = data_at SH T (if 254 =? i then a else b) p.
Proof. intros ; flatten. Qed.

Local Ltac solve_lengths H48 H4 H5 H6 H7 := repeat match goal with 
    | _ => omega
    | _ => rewrite H48
    | _ => rewrite H4
    | _ => rewrite H5
    | _ => rewrite H6
    | _ => rewrite H7
    | _ => rewrite upd_Znth_Zlength
    | _ => rewrite Zlength_app
  end.

Local Ltac solve_lengths2 := repeat match goal with 
    | _ => reflexivity
    | _ => omega
    | _ => rewrite undef16_Zlength
    | _ => rewrite Zlength_map
  end.

Lemma replace_list_app_app_app_app : forall i xx aa bb cc dd va vb vc vd,
  0 <= i < 16 ->
  Zlength aa = 16 ->
  Zlength bb = 16 ->
  Zlength cc = 16 ->
  Zlength dd = 16 ->
  Zlength xx = 16 ->
  Vlong va = Znth i (mVI64 aa) Vundef ->
  Vlong vb = Znth i (mVI64 bb) Vundef ->
  Vlong vc = Znth i (mVI64 cc) Vundef ->
  Vlong vd = Znth i (mVI64 dd) Vundef ->
  ((upd_Znth (i + 64)
     (upd_Znth (i + 48)
        (upd_Znth (i + 32)
           (upd_Znth (i + 16)
              (xx ++
               (firstn (nat_of_Z i) (mVI64 aa) ++ skipn (nat_of_Z i) undef16) ++
               (firstn (nat_of_Z i) (mVI64 cc) ++ skipn (nat_of_Z i) undef16) ++
               (firstn (nat_of_Z i) (mVI64 bb) ++ skipn (nat_of_Z i) undef16) ++
               firstn (nat_of_Z i) (mVI64 dd) ++ skipn (nat_of_Z i) undef16) (Vlong va)) 
           (Vlong vc)) (Vlong vb)) (Vlong vd))) =
  (xx ++
         (firstn (nat_of_Z (i + 1)) (mVI64 aa) ++ skipn (nat_of_Z (i + 1)) undef16) ++
         (firstn (nat_of_Z (i + 1)) (mVI64 cc) ++ skipn (nat_of_Z (i + 1)) undef16) ++
         (firstn (nat_of_Z (i + 1)) (mVI64 bb) ++ skipn (nat_of_Z (i + 1)) undef16) ++
         firstn (nat_of_Z (i + 1)) (mVI64 dd) ++ skipn (nat_of_Z (i + 1)) undef16).
Proof.
  intros i xx aa bb cc dd va vb vc vd Hi Haa Hbb Hcc Hdd Hxx Hva Hvb Hvc Hvd.

  assert(HZa: Zlength (firstn (nat_of_Z i) (mVI64 aa) ++ skipn (nat_of_Z i) undef16) = 16).
    rewrite take_drop_Zlength Zlength_map Zlength_map //.
  assert(HZb: Zlength (firstn (nat_of_Z i) (mVI64 bb) ++ skipn (nat_of_Z i) undef16) = 16).
    rewrite take_drop_Zlength Zlength_map Zlength_map //.
  assert(HZc: Zlength (firstn (nat_of_Z i) (mVI64 cc) ++ skipn (nat_of_Z i) undef16) = 16).
    rewrite take_drop_Zlength Zlength_map Zlength_map //.
  assert(HZd: Zlength (firstn (nat_of_Z i) (mVI64 dd) ++ skipn (nat_of_Z i) undef16) = 16).
    rewrite take_drop_Zlength Zlength_map Zlength_map //.

  assert(HZl80 : Zlength (xx ++
         (firstn (nat_of_Z i) (mVI64 aa) ++ skipn (nat_of_Z i) undef16) ++
         (firstn (nat_of_Z i) (mVI64 cc) ++ skipn (nat_of_Z i) undef16) ++
         (firstn (nat_of_Z i) (mVI64 bb) ++ skipn (nat_of_Z i) undef16) ++
         firstn (nat_of_Z i) (mVI64 dd) ++ skipn (nat_of_Z i) undef16) = 80).
  repeat rewrite Zlength_app ?HZa ?HZb ?HZc ?HZd ?Hxx //.
  rewrite (upd_Znth_comm val (i + 64) (i + 48) _ (Vlong vd) (Vlong vb)) ; try omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.

  rewrite (upd_Znth_comm val (i + 64) (i + 32) _ (Vlong vd) (Vlong vc)) ; try omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.

  rewrite (upd_Znth_comm val (i + 64) (i + 16) _ (Vlong vd) (Vlong va)) ; try omega.

  rewrite (upd_Znth_comm val (i + 48) (i + 32) _ (Vlong vb) (Vlong vc)) ; try omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.

  rewrite (upd_Znth_comm val (i + 48) (i + 16) _ (Vlong vb) (Vlong va)) ; try omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.

  rewrite (upd_Znth_comm val (i + 32) (i + 16) _ (Vlong vc) (Vlong va)) ; try omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.
  2: rewrite ?upd_Znth_Zlength HZl80; omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite Hxx.
  replace (i + 64 - 16) with (i + 48) by omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite Hxx.
  replace (i + 48 - 16) with (i + 32) by omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite Hxx.
  replace (i + 32 - 16) with (i + 16) by omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite Hxx.
  replace (i + 16 - 16) with i by omega.

  f_equal.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite HZa.
  replace (i + 48 - 16) with (i + 32) by omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite HZa.
  replace (i + 32 - 16) with (i + 16) by omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite HZa.
  replace (i + 16 - 16) with i by omega.

  rewrite upd_Znth_app1.
  2: solve_lengths HZa HZb HZc HZd Hxx.

  f_equal.

  rewrite ?simple_S_i ; try omega.
  rewrite Hva -upd_Znth_app_step_Zlength ; solve_lengths2.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite HZc.
  replace (i + 32 - 16) with (i + 16) by omega.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite HZc.
  replace (i + 16 - 16) with i by omega.

  rewrite upd_Znth_app1.
  2: solve_lengths HZa HZb HZc HZd Hxx.

  f_equal.

  rewrite ?simple_S_i ; try omega.
  rewrite Hvc -upd_Znth_app_step_Zlength ; solve_lengths2.

  rewrite upd_Znth_app2.
  2: solve_lengths HZa HZb HZc HZd Hxx.
  rewrite HZb.
  replace (i + 16 - 16) with i by omega.

  rewrite upd_Znth_app1.
  2: solve_lengths HZa HZb HZc HZd Hxx.

  f_equal;
  rewrite ?simple_S_i ; try omega;
  rewrite ?Hvd ?Hvb -upd_Znth_app_step_Zlength ; solve_lengths2.
Qed.

(* Definition sc_mult n p :=
  let p' := Unpack25519 p in
  let n' := clamp n in
  let m  := montgomery_fn 255 254 n' gf1 p' gf0 gf1 gf0 gf0 p' in
  let c  := get_c m in 
  let c' := Inv25519 c in 
  let a  := get_a m in
  Pack25519 (M a c').
 *)
Close Scope Z.
