(*
int crypto_scalarmult(u8 *q,const u8 *n,const u8 *p)
{
  u8 z[32];
  // i64 x[80],r,i;
  i64 r;
  int i;
  gf x,a,b,c,d,e,f;
  FOR(i,31) z[i]=n[i];
  z[31]=(n[31]&127)|64;
  z[0]&=248;
  unpack25519(x,p);
  FOR(i,16) {
    b[i]=x[i];
    d[i]=a[i]=c[i]=0;
  }
  a[0]=d[0]=1;
  for(i=254;i>=0;--i) {
    r=(z[i>>3]>>(i&7))&1;
    sel25519(a,b,r);
    sel25519(c,d,r);
    A(e,a,c);
    Z(a,a,c);
    A(c,b,d);
    Z(b,b,d);
    S(d,e);
    S(f,a);
    M(a,c,a);
    M(c,b,e);
    A(e,a,c);
    Z(a,a,c);
    S(b,a);
    Z(c,d,f);
    M(a,c,_121665);
    A(a,a,d);
    M(c,c,a);
    M(a,d,f);
    M(d,b,x);
    S(b,e);
    sel25519(a,b,r);
    sel25519(c,d,r);
  }
  inv25519(c,c);
  M(a,c,c);
  pack25519(q,a);
  return 0;
}
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_sel25519.
Require Import Tweetnacl_verif.spec_unpack25519.
Require Import Tweetnacl_verif.spec_pack25519.
Require Import Tweetnacl_verif.spec_A.
Require Import Tweetnacl_verif.spec_Z.
Require Import Tweetnacl_verif.spec_S.
Require Import Tweetnacl_verif.spec_M.
Require Import Tweetnacl_verif.spec_inv25519.
Require Import Tweetnacl_verif.spec_crypto_scalarmult.
Require Import Tweetnacl_verif.spec_pack25519.
Require Import Tweetnacl_verif.verif_crypto_scalarmult_lemmas.
Require Import Tweetnacl.Low.Export.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl.Low.Prep_n.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_rev.
Require Import Tweetnacl.Low.GetBit.
Require Import Tweetnacl.Low.Inv25519.
Require Import Tweetnacl.Low.Constant.
Require Import Tweetnacl.Low.Pack25519.
Require Import Tweetnacl.Low.Crypto_Scalarmult.
Require Import Tweetnacl.Low.Crypto_Scalarmult_.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Low.ScalarMult_rev.
Require Import Tweetnacl.Mid.Instances.
Require Import Tweetnacl.Gen.ABCDEF.

Open Scope Z.

Import Low.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs := 
      ltac:(with_library prog 
        [sel25519_spec; pack25519_spec;
         inv25519_spec; unpack25519_spec;
         A_spec; Z_spec; M_spec; S_spec]).

Definition _121665_contents := C_121665.

Ltac solve_montgomery_rec_rev_Zlength :=
  repeat match goal with
    | _ => omega
    | _ => rewrite Zlength_map
    | _ => rewrite Sel25519_Zlength
    | _ => rewrite M_Zlength
    | _ => rewrite Sq_Zlength
    | _ => rewrite A_Zlength
    | _ => rewrite Zub_Zlength
    | _ => rewrite fa_Zlength
    | _ => rewrite fb_Zlength
    | _ => rewrite fc_Zlength
    | _ => rewrite fd_Zlength
    | _ => rewrite fe_Zlength
    | _ => rewrite ff_Zlength
    | _ => rewrite get_a_montgomery_fn_Zlength
    | _ => rewrite get_b_montgomery_fn_Zlength
    | _ => rewrite get_c_montgomery_fn_Zlength
    | _ => rewrite get_d_montgomery_fn_Zlength
    | _ => rewrite get_e_montgomery_fn_Zlength
    | _ => rewrite get_f_montgomery_fn_Zlength
  end ; try reflexivity.

Local Ltac solve_montgomery_bounds :=
  repeat (split ; try assumption);
  match goal with
    | |- Forall _ _ => solve_bounds_by_values_Forall_impl
    | |- Zlength _ = _ => solve_montgomery_rec_rev_Zlength
    | |- _ => auto
   end.

Local Ltac solve_equiv_fabcdef i := 
  clean_context_from_VST;
  repeat match goal with
   | [H: context[Zlength] |- _ ] => clear H
   | [H: context[Forall] |- _ ] => clear H
   | [H: _ <> _ |- _ ] => clear H
  end;
  clears sh;
  rewrite -?fa_step -?fb_step -?fc_step -?fd_step -?fe_step -?ff_step;
  [| assumption];
  replace (254 - (254 - i)) with i ; [|omega];
  subst; simpl;
(*   rewrite /fa /fb /fc /fd /fe /ff; *)
(*   rewrite /ScalarMult_gen_small.fa /ScalarMult_gen_small.fb /ScalarMult_gen_small.fc; *)
(*   rewrite /ScalarMult_gen_small.fd /ScalarMult_gen_small.fe /ScalarMult_gen_small.ff; *)
  reflexivity.

Lemma body_crypto_scalarmult: semax_body Vprog Gprog f_crypto_scalarmult_curve25519_tweet crypto_scalarmult_spec.
Proof.
name v__121665 __121665.
  start_function.
unfold Sfor.
freeze [0;1;2;3;4;5;6;8;10;11] F.
freeze_local L.
forward_for_simple_bound 31 (crypto_scalarmult_Zinit_Inv F L sh v_z v_n n) ; subst L.
thaw_local.
- entailer!.
- forward.
  entailer!.
  clean_context_from_VST.
  solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
  forward.
  entailer!.
  clean_context_from_VST.
  unfold data_at.
  replace_cancel.

(*   symmetry. *)
  by apply firstn_skipn_upd_Znth_undef32.

  assert(0 < Zlength (firstn 31 n)).
  by apply Zlength_firstn_32_str_pos.

  assert(0 < Zlength (firstn 31 (map Vint (map Int.repr n)))).
  by rewrite -?map_firstn ?Zlength_map.

  assert(0 <= 31 < Zlength (firstn 31 (map Vint (map Int.repr n)) ++ [Vundef])).
  change 31%nat with (Z.to_nat 31).
  rewrite Zlength_app -?map_firstn ?Zlength_map ?Zlength_firstn ?Z.max_r ?Z.min_l ; simpl ; omega.
(* END OF FIRST FOR LOOP *)

forward. (* z[31]=(n[31]&127)|64; *)
entailer!.
clean_context_from_VST.
solve_bounds_by_values_f (fun x : ℤ => 0 <= x < 2 ^ 8).
forward.
forward.
entailer!.
clean_context_from_VST.
by apply isInt8Unsignedcontents_n.
simpl.
rewrite upd_Znth_diff ; try omega.
orewrite app_Znth1.
rewrite -?map_firstn map_map (Znth_map 0) ; try omega.

forward. (* z[0]&=248; *)
rewrite -clamped_n.
2: done.
2: done.

thaw F.
(* CALL FOR UNPACK25519 *)
rewrite /data_at_ /field_at_ /default_val /reptype_gen.
simpl.
assert(Hreadablesh: readable_share sh) by (by apply writable_readable).
assert(HwritableTsh : writable_share Tsh) by apply writable_share_top.
repeat match goal with
  | |- context[field_at Tsh lg16 [] ?A _] => change A with undef16
end.
match goal with
  | |- context[data_at Ews lg16 ?A _] => change A with (mVI64 C_121665)
end.
Ltac data_atify := repeat match goal with
  | |- context[field_at ?A ?B _ ?D ?E] => change (field_at A B [] D E) with (data_at A B D E)
end.
data_atify.
(* flatten_sepcon_in_SEP. *)
freeze [0; 1; 2; 3; 4; 5; 7; 9; 10] F.
sort.
forward_call (v_x, v_p, sh, Tsh, undef16 , p).
thaw F.
freeze_local L.
unfold Sfor.
assert(Zlength (Unpack25519 p) = 16).
by apply Unpack25519_Zlength.
freeze [0;2;3;8;9;10;11] F.
forward_for_simple_bound 16 (crypto_scalarmult_BDACinit_Inv F L sh v_x v_a v_b v_c v_d (Unpack25519 p)) ; subst L.
thaw_local.
entailer!.
assert(Haux1: exists aux1, Vlong aux1 = Znth i (map Vlong (map Int64.repr (Unpack25519 p))) Vundef)
  by (erewrite (Znth_map Int64.zero) ; [exists; reflexivity|]; rewrite Zlength_map; omega).
destruct Haux1 as [aux Haux].
forward ; rewrite -Haux.
entailer!.
do 6 forward.
rewrite ?map_firstn Haux.
rewrite <- (upd_Znth_app_step_Zlength i (map Vlong (map Int64.repr (Unpack25519 p)))) ; try omega.
unfold nat_of_Z ; rewrite ?Z2Nat.inj_succ.
replace (Z.to_nat (16 - (i + 1))) with (16 - S (Z.to_nat i))%nat.

2 : rewrite Z2Nat.inj_sub ; try omega ; rewrite Z2Nat.inj_succ ; try omega ; f_equal.
2: omega.
2: rewrite undef16_Zlength ; omega.
2: rewrite ?Zlength_map ; omega.
assert(H' := upd_Znth_app_step_Zlength i (mVI64 C_0) (undef16) Vundef).
rewrite ?H' ?undef16_Zlength ?Zlength_map ?nil16_Zlength ; try omega.

simpl cast_int_long.
replace (Znth i (mVI64 gf0) Vundef) with (Vlong (Int64.repr 0)).
2: clean_context_from_VST ; by apply Znth_nil16.
change nil16 with C_0.
entailer!.
rewrite ?list.drop_ge ?app_nil_r ?list.take_ge.

2: rewrite ?map_length ?nil16_length ; change 16%nat with (Z.to_nat 16) ; rewrite -Z2Nat.inj_le; omega.

2: {
rewrite ?map_length  Unpack25519_length.
change 16%nat with (Z.to_nat 16).
rewrite -Z2Nat.inj_le; omega.
rewrite Zlength_correct in H3.
omega.
}

2: rewrite undef16_length; change 16%nat with (Z.to_nat 16) ; rewrite -Z2Nat.inj_le; omega.

(* OUT OF THE SECOND LOOP *)
do 3 forward.

change ((upd_Znth 0
        (mVI64 nil16) (Vlong (cast_int_long Signed (Int.repr 1))))) with
         (map Vlong (map Int64.repr gf1)).

(* START THE BIG LOOP *)
thaw F.

change nil16 with C_0.
pose (Unpack25519 p) as x.
pose (gf1)  as a.
pose (Unpack25519 p) as b.
pose (gf0)  as c.
pose (gf1)  as d.
pose (Prep_n.clamp n) as z.
deadvars!.
data_atify.
change (data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr (Prep_n.clamp n))) v_z) with
 (data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr z)) v_z).
change (data_at Tsh (tarray tlg 16) (mVI64 (Unpack25519 p)) v_b) with
 (data_at Tsh (tarray tlg 16) (mVI64 (b)) v_b).
change (data_at Tsh (tarray tlg 16) (mVI64 gf1) v_a) with
 (data_at Tsh (tarray tlg 16) (mVI64 a) v_a).
change (data_at Tsh (tarray tlg 16) (mVI64 gf1) v_d) with
 (data_at Tsh (tarray tlg 16) (mVI64 d) v_d).
change (data_at Tsh (tarray tlg 16) (mVI64 nil16) v_c) with
 (data_at Tsh (tarray tlg 16) (mVI64 c) v_c).
change (data_at Tsh (tarray tlg 16) (mVI64 (Unpack25519 p)) v_x) with
 (data_at Tsh (tarray tlg 16) (mVI64 x) v_x).

freeze [0;3;6] F.

assert(Zlength(z) = 32). subst z; by apply Prep_n.clamp_Zlength.
assert(Zlength(a) = 16). subst a; reflexivity.
assert(Zlength(c) = 16). subst c; reflexivity.
assert(Zlength(d) = 16). subst d; reflexivity.
assert(Zlength(b) = 16). by subst b.
assert(Zlength(x) = 16). by subst x.
assert(Zlength(C_121665) = 16). reflexivity.

assert(Forall (fun x => 0 <= x < Z.pow 2 8) z).
  subst z. by apply Prep_n.clamp_bound.
assert(Forall (fun x => -38 <= x < Z.pow 2 16 + 38) a).
  subst a ; change (2^16 + 38) with 65574;
  repeat (rewrite list.Forall_cons ; split; [omega|]) ; apply Forall_nil.
assert(Forall (fun x => -38 <= x < Z.pow 2 16 + 38) b).
  subst b. eapply list.Forall_impl.
  by apply Unpack25519_bounded. intros y Hx ; simpl in Hx ; omega.
assert(Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c).
  subst c ; change (2^16 + 38) with 65574;
  repeat (rewrite list.Forall_cons ; split; [omega|]) ; apply Forall_nil.
assert(Forall (fun x => -38 <= x < Z.pow 2 16 + 38) d).
  subst d ; change (2^16 + 38) with 65574;
  repeat (rewrite list.Forall_cons ; split; [omega|]) ; apply Forall_nil.
assert(Forall (fun x => 0 <= x < Z.pow 2 16) x).
  by apply Unpack25519_bounded.
assert(Forall (fun x => 0 <= x < Z.pow 2 16) C_121665).
  unfold C_121665 ; repeat apply Forall_cons ; solve_bounds_by_values.
  apply Forall_nil.

forward_for 
(* Loop Invariant *)
(crypto_scalarmult_ladder_Inv F sh v_z v_x v_a v_b v_c v_d v_e v_f v_q z a b c d x c121665)
(* PreInc invariant *)
(crypto_scalarmult_ladder_PreIncInv F sh v_z v_x v_a v_b v_c v_d v_e v_f v_q z a b c d x c121665)
(* Loop postcondition *)
(crypto_scalarmult_ladder_PostInv F sh v_z v_x v_a v_b v_c v_d v_e v_f v_q z a b c d x c121665).

(* 6 sub goals are generated *)
(* 1 *)
forward.
unfold crypto_scalarmult_ladder_Inv.
Exists 254.
assert(H254: 254 = 254) by reflexivity.
apply Z.eqb_eq in H254.
rewrite /set_undef_array_sep ?H254.
change (254 - 254) with 0.
rewrite montgomery_fn_0 /get_a /get_b /get_c /get_d.

focus_SEP 0 4 6 5 7 8 2 1 9.
solve_bounds_by_values. (* this does nothing but if forces the 2^16 to be in Z and not in Z.pos ! *)
go_lowerx.
rewrite <- andp_assoc.
apply andp_right.
apply andp_right.
apply prop_right.
solve_montgomery_bounds ; omega.
apply prop_right.
repeat split; assumption.
cancel. (* Q |-- Q *)

(* 2 *)
rename a0 into i.
entailer!.
(* 3 *)
rename a0 into i.
assert(0 <= 254 - i) by omega.

Opaque two_p.
assert(Hidiv8: 0 <= i / two_p 3 <= 254 / two_p 3).
  apply i254div8bound ; omega.
assert(Hishr: (0 <= Int.unsigned (Int.shr (Int.repr i) (Int.repr 3)) < Zlength z)).
{
  replace (Zlength z) with 32.
  apply Intusignedshr32 ; omega.
}
assert(Hzlength: 0 <= i / two_p 3 < Zlength z).
{
  change (254 / two_p 3) with 31 in Hidiv8.
  omega.
}
assert(0 <= Z.land i 7 < 32).
  apply izland7_bound ; omega.
assert(HintluTrue : Int.ltu (Int.repr (Z.land i 7)) Int.iwordsize = true).
  apply Intltutrue ; omega.
forward.
entailer!.
solve_bounds_by_values_Znth.
orewrite Int.unsigned_repr.
solve_bounds_by_values.
rewrite Int.shr_div_two_p.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
rewrite (Int.unsigned_repr 3).
2: solve_bounds_by_values.
rewrite Int.unsigned_repr.
2: change (254 / two_p 3) with 31 in Hidiv8 ; solve_bounds_by_values.
forward.
entailer!.
rewrite HintluTrue ; simpl; trivial.
replace (force_val
               (sem_cast tint tlg
                  (eval_binop Oand tint tint
                     (eval_binop Oshr tuchar tint (Vint (Int.repr (Znth (i / two_p 3) z 0)))
                        (eval_binop Oand tint tint (Vint (Int.repr i)) (Vint (Int.repr 7)))) 
                     (Vint (Int.repr 1))))) with
  (Vlong (Int64.repr (Low.getbit i z))).

2:{
  clean_context_from_VST. clears v_a v_b v_c v_d v_e v_f.
  simpl.
  rewrite and_repr /tuchar /tint /sem_shift ; simpl.
  rewrite HintluTrue ; simpl.
  rewrite Int.shr_div_two_p.
  rewrite Int.unsigned_repr.
  2: solve_bounds_by_values.
  rewrite Int.signed_repr.
  2: solve_bounds_by_values_Znth.
  rewrite and_repr.
  assert(H0landdiv8: 0 <= Z.land (Znth (i / two_p 3) z 0 / two_p (Z.land i 7)) 1).
  {
  apply Z.land_nonneg ; right ; omega.
  }
  assert(Hlanddiv81: Z.land (Znth (i / two_p 3) z 0 / two_p (Z.land i 7)) 1 <= 1).
  {
  apply Z.log2_null.
  assert(Hlanddiv8min: Z.log2 (Z.land (Znth (i / two_p 3) z 0 / two_p (Z.land i 7)) 1) <=
        Z.min (Z.log2 (Znth (i / two_p 3) z 0 / two_p (Z.land i 7))) (Z.log2 1)).
  apply Z.log2_land.
  solve_bounds_by_values_Znth.
  apply Z_div_pos.
  apply two_p_gt_ZERO.
  apply Z.land_nonneg; right; omega.
  omega.
  omega.
  replace (Z.min (Z.log2 (Znth (i / two_p 3) z 0 / two_p (Z.land i 7))) (Z.log2 1)) with 0 in Hlanddiv8min.
  assert(Htemp := Z.log2_nonneg (Z.land (Znth (i / two_p 3) z 0 / two_p (Z.land i 7)) 1)).
  omega.
  simpl.
  rewrite Z.min_r.
  omega.
  apply Z.log2_nonneg.
  }
  rewrite Int.signed_repr.
  2: solve_bounds_by_values.
  rewrite /Low.getbit ?Z.shiftr_div_pow2 ?Znth_nth /nat_of_Z ?Z2Nat.id ?two_p_correct; try omega.
  reflexivity.
  apply Z_div_pos.
  reflexivity.
  omega.
  }
(*   apply Z.land_nonneg ; right ; omega. *)

  freeze [0;1;4;5;6;7;8;9] L.
  assert(Hgb:= getbit_0_or_1 i z).
  forward_call (v_a, v_b, Tsh,
  (get_a (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x)),
  (get_b (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x)), (Low.getbit i z)).
  repeat split;
  try rewrite get_a_montgomery_fn_Zlength;
  try rewrite get_b_montgomery_fn_Zlength; auto.
  omega.
  thaw L.

  freeze [0;1;2;3;6;7;8;9] L.
  forward_call (v_c, v_d, Tsh,
  (get_c (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x)),
  (get_d (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x)), (Low.getbit i z)).

  repeat split;
  try rewrite get_c_montgomery_fn_Zlength;
  try rewrite get_d_montgomery_fn_Zlength; auto.
  omega.
  thaw L.

  rewrite /set_undef_array_sep.

  remember (Low.Sel25519 (Low.getbit i z) (get_c (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))
                (get_d (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) as c0;
  remember (Low.Sel25519 (Low.getbit i z) (get_d (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))
           (get_c (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) as d0;
  remember (Low.Sel25519 (Low.getbit i z) (get_a (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))
           (get_b (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) as a0;
  remember (Low.Sel25519 (Low.getbit i z) (get_b (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))
           (get_a (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) as b0.
  assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) a0).
  {
    subst a0; clean_context_from_VST; apply Sel25519_bound_lt_le_id.
    apply get_a_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
    apply get_b_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
  }
  assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) b0).
  {
    subst b0; clean_context_from_VST; apply Sel25519_bound_lt_le_id.
    apply get_b_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
    apply get_a_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
  }
  assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) c0).
  {
    subst c0; clean_context_from_VST; apply Sel25519_bound_lt_le_id.
    apply get_c_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
    apply get_d_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
  }
  assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) d0).
  {
    subst d0; clean_context_from_VST; apply Sel25519_bound_lt_le_id.
    apply get_d_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
    apply get_c_montgomery_fn_bound ; auto.
    apply List_Z_Ops_Prop.
  }
  assert(Zlength a0 = 16). subst; solve_montgomery_rec_rev_Zlength.
  assert(Zlength b0 = 16). subst; solve_montgomery_rec_rev_Zlength.
  assert(Zlength c0 = 16). subst; solve_montgomery_rec_rev_Zlength.
  assert(Zlength d0 = 16). subst; solve_montgomery_rec_rev_Zlength.

  rewrite ?data_at_sh_if.
  remember (if 254 =? i then undef16 else mVI64 (get_f (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) as f0.
  assert(Zlength f0 = 16).
    subst f0 ; flatten ; solve_montgomery_bounds.
  remember (if 254 =? i then undef16 else mVI64 (get_e (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) as e0.
  assert(Zlength e0 = 16).
    subst e0 ; flatten ; solve_montgomery_bounds.
  replace (data_at Tsh (tarray tlg 16)
     (if 254 =? i then undef16 else mVI64 (get_e (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x)))
     v_e) with (data_at Tsh (tarray tlg 16) e0 v_e).
  2: by subst e0.
  replace (data_at Tsh (tarray tlg 16)
     (if 254 =? i then undef16 else mVI64 (get_f (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x)))
     v_f) with (data_at Tsh (tarray tlg 16) f0 v_f).
  2: by subst f0.

  freeze [1;3;4;5;7;8;9] L.

  forward_call (v_e, v_a, v_c, Tsh,Tsh,Tsh,
    e0, a0, -39, 2 ^ 16 + 38, c0, -39, 2 ^ 16 + 38, 4).
  unfold_nm_overlap_array_sep ; simpl; entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  clears e0. (* Heqe0 H57 e0. *)
  assert(Zlength (Low.A a0 c0) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;3;4;5;6;7;8;9] L.
  forward_call (v_a, v_a, v_c, Tsh,Tsh,Tsh,
    (mVI64 a0), a0, -39, 2 ^ 16 + 38, c0, -39, 2 ^ 16 + 38,0).
  unfold_nm_overlap_array_sep ; simpl; entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.Z a0 c0) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;2;5;6;7;8;9] L.
  forward_call (v_c, v_b, v_d, Tsh,Tsh,Tsh,
    (mVI64 c0), b0, -39, 2 ^ 16 + 38, d0, -39, 2 ^ 16 + 38,4).
  unfold_nm_overlap_array_sep ; simpl; entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.A b0 d0) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;3;4;5;6;7;8;9] L.
  forward_call (v_b, v_b, v_d, Tsh,Tsh,Tsh,
    (mVI64 b0), b0, -39, 2 ^ 16 + 38, d0, -39, 2 ^ 16 + 38,0).
  unfold_nm_overlap_array_sep ; simpl;entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.Z b0 d0) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;2;3;5;6;7;8;9] L.
  forward_call (v_d, v_e, Tsh,Tsh,
    (mVI64 d0), (Low.A a0 c0),1).
  unfold_nm_overlap_array_sep ; simpl;entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  freeze [0;1;2;3;5;6;8;9] L.
  forward_call (v_f, v_a, Tsh,Tsh,
    f0, (Low.Z a0 c0),1).
  unfold_nm_overlap_array_sep ; simpl;entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

(*   clear Heqf0 H55 f0. *)
  clears f0.

  freeze [0;2;3;4;6;7;8;9] L.
  forward_call (v_a, v_c, v_a, Tsh, Tsh, Tsh,
    (mVI64 (Low.Z a0 c0)), (Low.A b0 d0), (Low.Z a0 c0),1).
  unfold_nm_overlap_array_sep ; simpl;entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.M (Low.A b0 d0) (Low.Z a0 c0)) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;2;3;6;7;8;9] L.
  forward_call (v_c, v_b, v_e, Tsh, Tsh, Tsh,
    (mVI64 (Low.A b0 d0)), (Low.Z b0 d0), (Low.A a0 c0),4).
  unfold_nm_overlap_array_sep ; simpl;entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.M (Low.Z b0 d0) (Low.A a0 c0)) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [1;4;5;6;7;8;9] L.
  remember (Low.M (Low.Z b0 d0) (Low.A a0 c0)) as c1.
  remember (Low.M (Low.A b0 d0) (Low.Z a0 c0)) as a1.
  assert(Zlength c1 = 16). auto.
  assert(Zlength a1 = 16). auto.
  forward_call (v_e, v_a, v_c, Tsh, Tsh, Tsh,
    (mVI64 (Low.A a0 c0)), a1, -39, 2 ^ 16 + 38, c1, -39, 2 ^ 16 + 38, 4).
  unfold_nm_overlap_array_sep ; simpl.
  cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.A a1 c1) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;3;4;5;6;7;8;9] L.
  forward_call (v_a, v_a, v_c, Tsh, Tsh, Tsh,
    (mVI64 a1), a1, -39, 2 ^ 16 + 38, c1, -39, 2 ^ 16 + 38, 0).
  unfold_nm_overlap_array_sep ; simpl.
  cancel.
  entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.Z a1 c1) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [1;2;4;5;6;7;8;9] L.
  forward_call (v_b, v_a, Tsh, Tsh,
    (mVI64 (Low.Z b0 d0)), (Low.Z a1 c1), 1).
  unfold_nm_overlap_array_sep ; simpl; cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  freeze [0;1;3;6;7;8;9] L.
  remember (Low.S (Low.A a0 c0)) as d1.
  remember (Low.S (Low.Z a0 c0)) as f1.
  assert(Zlength d1 = 16). auto.
  assert(Zlength d1 = 16). auto.

  forward_call (v_c, v_d, v_f, Tsh, Tsh, Tsh,
   (mVI64 c1) , d1, -39, 2 ^ 16 + 38, f1, -39, 2 ^ 16 + 38, 4).
  unfold_nm_overlap_array_sep ; simpl; cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.Z d1 f1) = 16).
    solve_montgomery_rec_rev_Zlength.

  sort.

  freeze [1;2;3;5;6;7;8] L.
  remember (Low.Z a1 c1) as a2.
  remember (Low.Z d1 f1) as c2.
  assert(Zlength a2 = 16). auto.
  assert(Zlength c2 = 16). auto.

  forward_call (v_a, v_c, c121665, Tsh, Tsh, Ews,
   (mVI64 a2) , c2, C_121665,4).
  unfold_nm_overlap_array_sep ; simpl; cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.M c2 C_121665) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [1;2;4;5;6;7;8;9] L.
  remember (Low.M c2 C_121665) as a3.
  assert(Zlength a3 = 16). auto.

  forward_call (v_a, v_a, v_d, Tsh, Tsh, Tsh,
   mVI64 a3, a3, -39, 2 ^ 16 + 38, d1, -39, 2 ^ 16 + 38,0).
  unfold_nm_overlap_array_sep ; simpl;
  cancel.
  entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.A a3 d1) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [1;3;4;5;6;7;8;9] L.
  forward_call (v_c, v_c, v_a, Tsh, Tsh, Tsh,
   (mVI64 c2) , c2, (Low.A a3 d1),0).
  unfold_nm_overlap_array_sep ; simpl; cancel.
  entailer!.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  freeze [0;3;5;6;7;8;9] L.
  forward_call (v_a, v_d, v_f, Tsh, Tsh, Tsh,
   (mVI64 (Low.A a3 d1)) , d1, f1,4).
  unfold_nm_overlap_array_sep ; simpl; cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.M d1 f1) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;2;3;4;6;7;8] L.
  remember (Low.S a2) as b1.
  assert(Zlength b1 = 16). auto.
  forward_call (v_d, v_b, v_x, Tsh, Tsh, Tsh,
   (mVI64 d1), b1, x,4).
  unfold_nm_overlap_array_sep ; simpl; cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  assert(Zlength (Low.M b1 x) = 16).
    solve_montgomery_rec_rev_Zlength.

  freeze [0;2;3;4;5;6;8;9] L.
  forward_call (v_b, v_e, Tsh,Tsh,
   mVI64 b1, Low.A a1 c1,1).
  unfold_nm_overlap_array_sep ; simpl;
  cancel.
  solve_montgomery_bounds.
  unfold_nm_overlap_array_sep ; simpl.
  thaw L.

  remember (Low.S (Low.A a1 c1)) as b2.
  remember (Low.M d1 f1) as a4.
  forward_call (v_a, v_b, Tsh, a4, b2, (Low.getbit i z)).
  solve_montgomery_bounds.
  omega.

  assert(Zlength (Low.M c2 (Low.A a3 d1)) = 16).
    solve_montgomery_rec_rev_Zlength.
  remember(Low.M c2 (Low.A a3 d1)) as c3.
  assert(Zlength c3 = 16). auto.
  remember (Low.M b1 x) as d2.
  assert(Zlength d2 = 16). auto.
  forward_call (v_c, v_d, Tsh, c3, d2, (Low.getbit i z)).
  solve_montgomery_bounds.
  omega.

  (* END OF THE LOOP *)
  (* We must now entail the loop. *)
  (* in other word prove a property correct before the increment but after the first loop *)
  (* In other word crypto_scalarmult_ladder_PreIncInv must be true for i = 254 but after the first loop *)

  (* CURRENT PROPERTY IS WRONG *)
  unfold crypto_scalarmult_ladder_PreIncInv.
  Exists i.
  replace (254 - (i - 1)) with ((254 - i) + 1).
  2: omega.
  remember (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x) as m0.
  replace (get_a (montgomery_fn List_Z_Ops ((254 - i) + 1) 254 z a b c d nil16 nil16 x)) 
    with (Low.Sel25519 (Low.getbit i z) a4 b2).
  replace (get_b (montgomery_fn List_Z_Ops ((254 - i) + 1) 254 z a b c d nil16 nil16 x)) 
    with (Low.Sel25519 (Low.getbit i z) b2 a4).
  replace (get_c (montgomery_fn List_Z_Ops ((254 - i) + 1) 254 z a b c d nil16 nil16 x)) 
    with (Low.Sel25519 (Low.getbit i z) c3 d2).
  replace (get_d (montgomery_fn List_Z_Ops ((254 - i) + 1) 254 z a b c d nil16 nil16 x)) 
    with (Low.Sel25519 (Low.getbit i z) d2 c3).
  replace (get_e (montgomery_fn List_Z_Ops ((254 - i) + 1) 254 z a b c d nil16 nil16 x)) 
    with (Low.A a1 c1).
  replace (get_f (montgomery_fn List_Z_Ops ((254 - i) + 1) 254 z a b c d nil16 nil16 x)) 
    with (f1).

(*   solve_bounds_by_values. (* this does nothing but if forces the 2^16 to be in Z and not in Z.pos ! *) *)
  remember (Low.Sel25519 (Low.getbit i z) c3 d2) as c'.
  remember (Low.Sel25519 (Low.getbit i z) d2 c3) as d'.
  remember (Low.A a1 c1) as e'.
  remember (Low.Sel25519 (Low.getbit i z) a4 b2) as a'.
  remember (Low.Sel25519 (Low.getbit i z) b2 a4) as b'.
(*   Opaque c_121665. *)
  (* this is sper slow with cancel and entailer, better do it manually *)
  focus_SEP 8 9 2 3 0 1 4 6 5.
  solve_bounds_by_values. (* this does nothing but if forces the 2^16 to be in Z and not in Z.pos ! *)
  go_lowerx.
  rewrite <- andp_assoc.
  apply andp_right.
  apply andp_right.
  apply prop_right.
  solve_montgomery_bounds ; omega.
  apply prop_right.
  repeat split ; assumption.
  cancel. (* Q |-- Q *)

  solve_equiv_fabcdef i.   (* f equiv *)
  solve_equiv_fabcdef i.   (* e equiv *)
  solve_equiv_fabcdef i.   (* d equiv *)
  solve_equiv_fabcdef i.   (* c equiv *)
  solve_equiv_fabcdef i.   (* b equiv *)
  solve_equiv_fabcdef i.   (* a equiv *)

  (* GOAL 5 *)
  (* INCREMENT *)
  rename a0 into i.
  forward.
  (* END OF THE FOR *)
  (* We must now entail the for. *)
  (* in other word prove a property correct AFTER the increment but after the first loop *)
  (* In other word crypto_scalarmult_ladder_PreIncInv must be true for i < 254 but after the first loop *)
  rewrite sub_repr.
  Exists (i - 1).
  rewrite /set_undef_array_sep.
  assert(H254false: (254 =? i - 1) = false).
  {
    clean_context_from_VST.
    apply Z.eqb_neq; omega.
  }
  rewrite H254false.
  (* this is sper slow with cancel and entailer, better do it manually *)
  solve_bounds_by_values. (* this does nothing but if forces the 2^16 to be in Z and not in Z.pos ! *)
  go_lowerx.
  rewrite <- andp_assoc.
  apply andp_right.
  apply andp_right.
  apply prop_right.
  solve_montgomery_bounds ; omega.
  apply prop_right.
  repeat split ; assumption.
  cancel. (* Q |-- Q *)

  (* GOAL 6 *)
  rename a0 into i.
  assert(Hi: i = -1).
  omega.
  rewrite Hi.
  change (254 - -1) with 255.
  unfold crypto_scalarmult_ladder_PostInv.
  rewrite /set_undef_array_sep.
  assert(H254false: (254 =? - 1) = false).
  {
    clean_context_from_VST.
    apply Z.eqb_neq; omega.
  }
  rewrite H254false.

  (* this is sper slow with cancel and entailer, better do it manually *)
  remember (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x) as m. (* prevent some computing... *)
  go_lowerx.
  rewrite <- andp_assoc.
  apply andp_right.
  apply andp_right.
  apply prop_right.
  solve_montgomery_bounds ; omega.
  apply prop_right.
  repeat split ; assumption.
  cancel. (* Q |-- Q *)
  thaw F.

   freeze [0; 1; 2; 3; 4; 5; 7; 8; 9; 10; 11] F.
   remember (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x) as m.
   remember (get_c m) as cc.
   remember (get_a m) as aa.
   assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) cc).
     subst; apply get_c_montgomery_fn_bound ; try assumption.
    apply List_Z_Ops_Prop.
    omega.
   assert(Zlength cc = 16).
     subst; rewrite get_c_montgomery_fn_Zlength ; try assumption ; omega.
   assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) aa).
     subst; apply get_a_montgomery_fn_bound ; try assumption.
    apply List_Z_Ops_Prop.
    omega.
   assert(Zlength aa = 16).
     subst; rewrite get_a_montgomery_fn_Zlength; try assumption.
    omega.

   (* inv25519(c,c); *)
   forward_call (v_c, v_c, Tsh, Tsh, mVI64 cc, cc, 0).
   unfold_nm_overlap_array_sep ; simpl;entailer!.
   solve_montgomery_bounds.
   unfold_nm_overlap_array_sep.
   change (0 =? 0) with true.
   flatten.
   thaw F.
   remember (Inv25519.Inv25519 cc) as ccc.
   freeze [1; 2; 3; 4; 6; 7; 8; 9; 10; 11] L.

   (*  M(a,a,c); *)
   forward_call (v_a, v_a, v_c, Tsh, Tsh, Tsh,
   (mVI64 aa) , aa, ccc, 0).
   unfold_nm_overlap_array_sep ; simpl;entailer!.
   solve_montgomery_bounds.
   unfold_nm_overlap_array_sep ; simpl.
   thaw L.

  deadvars!.

  freeze [1;2;4;5;6;7;8;9;10;11] F.
  forward_call (v_q, v_a, Tsh, sh, q, (Low.M aa ccc)).
  repeat (split ; try assumption).
  apply writable_readable ; auto.
  solve_bounds_by_values_Forall_impl.
  apply M_Zlength ; try assumption.
  thaw F.
  replace (Pack25519 (Low.M aa ccc)) with (Crypto_Scalarmult n p).
  deadvars!.
  unfold POSTCONDITION.
  unfold abbreviate.
  remember (Crypto_Scalarmult n p) as sc.
  eapply (semax_return_Some _ _ _ _ _ (stackframe_of f_crypto_scalarmult_curve25519_tweet) 
    [Tsh [{v_a}]<<( lg16 )-- undef16; Tsh [{v_c}]<<( lg16 )-- undef16; 
Tsh [{v_z}]<<( uch32 )-- undef32; Tsh [{v_b}]<<( lg16 )-- undef16; Tsh [{v_d}]<<( lg16 )-- undef16;
Tsh [{v_e}]<<( lg16 )-- undef16; Tsh [{v_f}]<<( lg16 )-- undef16; Tsh [{v_x}]<<( lg16 )-- undef16] _ _ _ (Vint (Int.repr 0))).
  go_lowerx.
  entailer!.
  entailer!.
  3: apply return_inner_gen_canon_Some.
  change (ret_type Delta) with tint.
  apply return_outer_gen_refl.

  2: change ([sh [{v_q}]<<( uch32 )-- mVI64 (sc);
          sh [{v_n}]<<( uch32 )-- mVI n; sh [{v_p}]<<( uch32 )-- mVI p;
          Ews [{c121665}]<<( lg16 )-- mVI64 C_121665] ++
          [Tsh [{v_a}]<<( lg16 )-- undef16; Tsh [{v_c}]<<( lg16 )-- undef16; Tsh [{v_z}]<<( uch32 )-- undef32; Tsh [{v_b}]<<( lg16 )-- undef16;
          Tsh [{v_d}]<<( lg16 )-- undef16; Tsh [{v_e}]<<( lg16 )-- undef16; Tsh [{v_f}]<<( lg16 )-- undef16;
          Tsh [{v_x}]<<( lg16 )-- undef16]) with
        ([sh [{v_q}]<<( uch32 )-- mVI64 (sc);
          sh [{v_n}]<<( uch32 )-- mVI n; sh [{v_p}]<<( uch32 )-- mVI p;
          Ews [{c121665}]<<( lg16 )-- mVI64 c_121665 ; Tsh [{v_a}]<<( lg16 )-- undef16; Tsh [{v_c}]<<( lg16 )-- undef16;
          Tsh [{v_z}]<<( uch32 )-- undef32; Tsh [{v_b}]<<( lg16 )-- undef16; Tsh [{v_d}]<<( lg16 )-- undef16; 
          Tsh [{v_e}]<<( lg16 )-- undef16; Tsh [{v_f}]<<( lg16 )-- undef16; Tsh [{v_x}]<<( lg16 )-- undef16]).
  2: change ([Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 8) (sc);
       Zlength (sc) = 32] ++ [Vint (Int.repr 0) = Vint Int.zero]) with
        ([Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 8) (sc);
       Zlength (sc) = 32; Vint (Int.repr 0) = Vint Int.zero]).

  focus_SEP 2 7 0 3 1 4 5 6.
  eapply canonicalize_stackframe.
  reflexivity.
  repeat (apply Forall2_cons ; [apply fn_data_at_intro ; reflexivity|]).
  apply Forall2_nil.
  go_lowerx.
  rewrite <- andp_assoc.
  apply andp_right.
  apply andp_right.
  apply prop_right.
  2: by apply prop_right.
  2: cancel. (* Q |-- Q *)
  2: subst aa ccc m cc a b c d x z.
  2: reflexivity.
  subst sc.
  split ; [|split]; rewrite /Crypto_Scalarmult.
  3: split ; trivial.
  all: rewrite -?Heqm -?Heqcc -?Heqaa  -?Heqccc.
  apply Pack25519_bound.
  apply M_Zlength ; assumption.
  solve_bounds_by_values_Forall_impl.
  rewrite /Pack25519.
  apply Pack.pack_for_Zlength_32_16.
  apply Reduce_by_P.get_t_subst_select_Zlength.
  omega.
  reflexivity.
  do 3 apply car25519_Zlength.
  apply M_Zlength ; assumption.
Qed.
