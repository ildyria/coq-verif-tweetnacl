Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_sel25519.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Sel25519.
Require Import Tweetnacl.Low.Binary_select.

Open Scope Z.

Import Low.

(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
      ltac:(with_library prog [sel25519_spec]).

Lemma body_sel25519: semax_body Vprog Gprog f_sel25519 sel25519_spec.
Proof.
start_function.
forward.
unfold Sfor.
simpl.
assert(Hqqq: (Datatypes.length contents_q = 16)%nat).
move: H H0 ; rewrite ?Zlength_correct => H H0; omega.
assert(Hppp: (Datatypes.length contents_p = 16)%nat).
move: H H0 ; rewrite ?Zlength_correct => H H0; omega.
rewrite Int.sub_signed.
rewrite Int.signed_repr.
rewrite Int.signed_repr.
2: solve_bounds_by_values.
2: destruct H1 ; subst b ; solve_bounds_by_values.
rewrite /Int.not.

rewrite /Int.mone.
replace (Int.xor (Int.repr (b - 1)) (Int.repr (-1))) with 
(Int.repr (Z.lxor (b - 1) (-1))).
2:{
move: H1 => [] -> //= ; change (Int.repr 0) with Int.zero ; rewrite Int.xor_zero_l //.
}
assert(Hbb: (Z.lxor (b - 1) (-1)) = 0 \/ (Z.lxor (b - 1) (-1)) = -1).
{
move: H1 => [] -> /= ; auto.
}
rewrite Int.signed_repr.
2: move: Hbb => [] -> ; solve_bounds_by_values.
assert(Hc: exists c, c = (Int64.repr (Z.lxor (b - 1) (-1)))) by (eexists; reflexivity).
destruct Hc as [c Hc] ; rewrite <- Hc.
assert(c = Int64.repr (set_xor b)).
{
destruct H1 ; subst ; rewrite ?set_xor_0 ?set_xor_1 ?H2 ?H3 => //=.
}
assert(Hd: exists d, d = set_xor b) by (eexists; reflexivity).
destruct Hd as [d Hd].
forward_for_simple_bound 16 (sel25519_Inv sh p q b d contents_p contents_q).
- rewrite ?skipn_0 ?firstn_O ?app_nil_l.
  rewrite ?H2.
  entailer!.
- assert(Z.of_nat (nat_of_Z i) < 16) by (rewrite Z2Nat.id ; omega).
  assert(Hp': exists p', Vlong p' = (Znth i (map Vlong (map Int64.repr (firstn (nat_of_Z i) (Sel25519 b contents_p contents_q) ++ skipn (nat_of_Z i) contents_p))) Vundef)).
  {
  eexists.
  rewrite (Znth_map Int64.zero).
  reflexivity.
    rewrite Zlength_map take_drop_Zlength -Sel25519_Zlength_eq; omega.
  }
  destruct Hp' as [p' Hp'].
  forward ; rewrite <- Hp'.
  entailer!.
  assert(Hq': exists q', Vlong q' = (Znth i (map Vlong (map Int64.repr (firstn (nat_of_Z i) (Sel25519 b contents_q contents_p) ++ skipn (nat_of_Z i) contents_q))) Vundef)).
  {
  eexists.
  rewrite (Znth_map Int64.zero).
  reflexivity.
    rewrite Zlength_map take_drop_Zlength -Sel25519_Zlength_eq; omega.
  }
  destruct Hq' as [q' Hq'].
  forward ; rewrite <- Hq'.
  entailer!.
  forward.
  forward ; rewrite <- Hp'.
  entailer!.
  forward.
  forward ; rewrite <- Hq'.
  entailer!.
  forward.
  entailer!.
  clean_context_from_VST.
  repeat orewrite simple_S_i.
  rewrite upd_Znth_map.
  move: Hp' Hq'.
  rewrite ?(Znth_map Int64.zero).
  2: (rewrite Zlength_map take_drop_Zlength -Sel25519_Zlength_eq; omega).
  2: (rewrite Zlength_map take_drop_Zlength -Sel25519_Zlength_eq; omega).
  move => Hp' Hq'.
  inversion Hp'.
  inversion Hq'.
  destruct H1; subst b.
  + repeat rewrite set_xor_0.
    repeat rewrite Int64.and_zero_l.
    repeat rewrite Int64.xor_zero.
    repeat match goal with 
      | _ => rewrite upd_Znth_map
      | _ => rewrite (Znth_map 0)
      | _ => rewrite take_drop_Zlength; rewrite <- Sel25519_Zlength_eq ; omega
    end.
    change (Sel25519 0 contents_q contents_p) with contents_q.
    change (Sel25519 0 contents_p contents_q) with contents_p.
    replace ((Znth i
               (firstn (nat_of_Z i) contents_p ++
                skipn (nat_of_Z i) contents_p) 0)) with 
    (Znth i contents_p 0) by (rewrite list.take_drop; reflexivity).
    replace ((Znth i
               (firstn (nat_of_Z i) contents_q ++
                skipn (nat_of_Z i) contents_q) 0)) with 
    (Znth i contents_q 0) by (rewrite list.take_drop; reflexivity).
    rewrite <- (upd_Znth_app_step_Zlength _ _ _ 0) by omega.
    repeat rewrite <- (upd_Znth_app_step_Zlength _ _ _ 0) by omega.
    cancel.
    rewrite set_xor_1.
    rewrite Int64.and_mone_l.
(*     clear H7 Hq' Hp'. *)
    rewrite upd_Znth_map.
    repeat match goal with 
      | _ => rewrite (Znth_map 0)
      | _ => rewrite take_drop_Zlength; rewrite <- Sel25519_Zlength_eq ; omega
      | _ => rewrite Znth_nth ; try omega
    end.
    change (Sel25519 1 contents_q contents_p) with contents_p.
    change (Sel25519 1 contents_p contents_q) with contents_q.
    orewrite nth_take.
    orewrite nth_take.
    rewrite <- nth_drop_2 by omega.
    rewrite <- nth_drop_2 by omega.
    rewrite <- Int64.xor_assoc.
    rewrite Int64.xor_idem Int64.xor_zero_l Int64.xor_commut Int64.xor_assoc Int64.xor_idem Int64.xor_zero.
    repeat rewrite <- Znth_nth by omega.
    repeat match goal with 
      | _ => rewrite upd_Znth_map
      | _ => rewrite (Znth_map 0)
      | _ => rewrite take_drop_Zlength; rewrite <- Sel25519_Zlength_eq ; omega
    end.
    repeat rewrite <- (upd_Znth_app_step_Zlength _ _ _ 0) by omega.
    cancel.
- forward.
  clean_context_from_VST.
  rewrite Zlength_correct in H, H0.
  assert(Hq: (Datatypes.length contents_q = 16)%nat) by omega.
  assert(Hp: (Datatypes.length contents_p = 16)%nat) by omega.
  repeat match goal with
    | _ => rewrite list.take_ge
    | _ => rewrite list.drop_ge
    | _ => rewrite app_nil_r; cancel
    | _ => rewrite Hq
    | _ => rewrite Hp
    | _ => rewrite <- Sel25519_length_eq
    | _ => change (Pos.to_nat 16) with 16%nat
  end ; omega.
Qed.
