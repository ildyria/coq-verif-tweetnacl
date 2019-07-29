Set Warnings "-notation-overridden,-parsing".
From Tweetnacl_verif Require Import init_tweetnacl.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Pack25519.
From Tweetnacl.Low Require Import Pack.
From Tweetnacl.Low Require Import Reduce_by_P.
From Tweetnacl.Low Require Import Reduce_by_P_aux.
From Tweetnacl.Low Require Import Reduce_by_P_compose_step.
From Tweetnacl.Low Require Import GetBit_pack25519.
From Tweetnacl.Low Require Import Sel25519.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Car25519.
From Tweetnacl.Low Require Import Car25519_bounds.
From Tweetnacl_verif Require Import spec_set25519.
From Tweetnacl_verif Require Import spec_sel25519.
From Tweetnacl_verif Require Import spec_car25519.
From Tweetnacl_verif Require Import spec_pack25519.

Open Scope Z.

Definition Gprog : funspecs :=
      ltac:(with_library prog [pack25519_spec; car25519_spec; set25519_spec; sel25519_spec]).

Lemma bound_impl_247_262: forall x : ℤ, 38 * - 2 ^ 47 <= x < 2 ^ 16 + 38 * 2 ^ 47 -> - 2 ^ 62 < x < 2 ^ 62.
Proof. intros. solve_bounds_by_values. Qed.

Lemma verif_pack25519_1: forall Tsh n,
  writable_share Tsh ->
  Zlength n = 16 ->
  Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) n ->
  writable_share Tsh /\ Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) (car25519 n) /\ Zlength (car25519 n) = 16.
Proof.
intros Tsh n HTsh Hln Hbn.
repeat match goal with
| _ => assumption
| _ => apply bound_impl_247_262
| [ |- _ /\ _ ] => split
| _ => solve[rewrite car25519_Zlength ; auto]
| _ => apply Zcar25519_bounds_length_1
| _ => solve[rewrite Zlength_correct in Hln ; omega]
| _ => eapply list.Forall_impl
end.
Qed.

Lemma verif_pack25519_2:
forall Tsh n,
  writable_share Tsh ->
  Zlength n = 16 ->
  Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) n ->
writable_share Tsh /\
Forall (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62) (car25519 (car25519 n)) /\ Zlength (car25519 (car25519 n)) = 16.
Proof.
intros Tsh n HTsh Hln Hbn.
repeat match goal with
| _ => assumption
| _ => apply bound_impl_247_262
| [ |- _ /\ _ ] => split
| _ => solve[rewrite ?car25519_Zlength ; auto]
| _ => apply Zcar25519_bounds_length_1
| _ => solve[rewrite Zlength_correct in Hln ; omega]
| _ => eapply list.Forall_impl
| _ => rewrite ?car25519_length
end.
Qed.

(* 
Lemma verif_pack25519_3:
forall F,
OracleKind ->
forall (v_o v_n : val) (tsh : share) (contents_o : list val) (n : list ℤ) (v_t v_m : val),
writable_share tsh ->
Zlength n = 16 ->
writable_share Tsh ->
forall t : list ℤ,
Zlength t = 16 ->
ENTAIL initialized_list [] (func_tycontext f_pack25519 Vprog Gprog []),
PROP ( )
LOCAL (lvar _m lg16 v_m; lvar _t lg16 v_t; temp _o v_o)
SEP (FRZL F ; Tsh [{v_t}]<<( lg16 )-- mVI64 t;
Tsh [{v_m}]<<( lg16 )-- mVI64 nil16)
|-- PROP (writable_share Tsh; Zlength nil16 = 16; Zlength t = 16; 0 >= 0)
    LOCAL (lvar _m lg16 v_m; lvar _t lg16 v_t; temp _o v_o)
    SEP (FRZL F;
    Tsh [{v_t}]<<( lg16 )-- mVI64 (get_t (nil16, t)); Tsh [{v_m}]<<( lg16 )-- mVI64 (get_m (nil16, t))).
Proof.
intros.
entailer.
Qed.
 *)
Lemma verif_pack25519_4:
forall t',
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t'->
Int64.min_signed <= Znth 0 t' 0 - 65517 <= Int64.max_signed.
Proof.
intros.
assert(Int64.min_signed + 65517 <= Znth 0 t' 0  <= Int64.max_signed  + 65517).
solve_bounds_by_values_Znth.
omega.
Qed.

Lemma verif_pack25519_5':
forall t' : list ℤ,
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
forall i : ℤ,
1 <= i < 15 ->
forall m''' : list ℤ,
Zlength m''' = 16 ->
Zlength (mVI64 m''') = 16 ->
Zlength (mVI64 t') = 16 ->
Int64.min_signed <=
Znth i t' 0 - 65535 -
Int64.signed (Int64.and (Int64.shr (Int64.repr (Znth (i - 1) m''' 0)) (Int64.repr 16)) (Int64.repr 1)) <=
Int64.max_signed /\ Int64.min_signed <= Int64.signed (Int64.repr (Znth i t' 0)) - 65535 <= Int64.max_signed.
Proof.
split.
2: solve_bounds_by_values_Znth.
rewrite and64_repr.
remember (Z.shiftr (Int64.signed (Int64.repr (Znth (i - 1) m''' 0))) (Int64.unsigned (Int64.repr 16))) as mi1.
assert(0 <= Z.land mi1 1 <= 1) by apply and_0_or_1.
assert(HZland: Z.land mi1 1 = 0 \/ Z.land mi1 1 = 1) by omega.
destruct HZland as [HZland | HZland]; rewrite HZland.
1,2: assert(Int64.min_signed + 65536 <= Znth i t' 0 <= Int64.max_signed  + 65535) by
solve_bounds_by_values_Znth.
all: rewrite ?Int64.signed_repr.
all: solve_bounds_by_values.
Qed.

Lemma verif_pack25519_6:
forall t' : list ℤ,
forall m' : list ℤ,
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
Zlength m' = 16 ->
forall m'' : list ℤ,
m'' = upd_Znth 0 m' (Znth 0 t' 0 - 65517) ->
Zlength m'' = 16 ->
forall i : ℤ,
1 <= i < 15 ->
forall m''' : list ℤ,
m''' = sub_fn_rev 1 sub_step i m'' t' ->
Zlength m''' = 16 ->
Int64.min_signed <= Znth (i - 1) m''' 0 <= Int64.max_signed.
Proof.
intros.
repeat match goal with
  | [ H: context[Znth] |- _ ]=> rewrite Znth_nth in H
  | [ |- context[Znth] ]=> rewrite Znth_nth
  | _ => omega
end.
match goal with | [ |- context[nth ?a ?b ?c]] => replace (nth a b c) with (nth a b 0) end.
match goal with | [ H: context[nth ?a ?b ?c] |- _ ] => replace (nth a b c) with (nth a b 0) in H end.
2,3: apply nth_indep.
2,3: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2,3: rewrite /nat_of_Z ; apply Z2Nat.inj_lt ; rewrite -?Zlength_correct ; omega.
subst m'''.
subst m''.
orewrite upd_Znth_upd_nth.
rewrite {2 4}/nat_of_Z.
repeat change_Z_to_nat.
assert(- 2 ^ 16 <= nth (nat_of_Z (i - 1)) (sub_fn_rev 1 sub_step i (upd_nth 0 m' (nth 0 t' 0 - 65517)) t') 0 < 2 ^ 16).
apply sub_fn_rev_f_bound_nth ; try assumption.
omega.
match goal with | [ |- _ <= ?a <= _ ] => remember a as blabla end.
solve_bounds_by_values.
Qed.

Lemma verif_pack25519_7:
forall t' : list ℤ,
forall m'' : list ℤ,
Zlength m'' = 16 ->
forall i : ℤ,
1 <= i < 15 ->
forall m''' : list ℤ,
m''' = sub_fn_rev 1 sub_step i m'' t' ->
Zlength m''' = 16 ->
sub_fn_rev 1 sub_step (i + 1) m'' t' =
upd_Znth (i - 1) (upd_Znth i m''' (Znth i t' 0 - 65535 - Z.land (Znth (i - 1) m''' 0 / two_p 16) 1))
  (Z.land (Znth (i - 1) m''' 0) 65535).
Proof.
intros.
rewrite sub_fn_rev_n.
2: omega.
replace (i + 1 - 1) with i.
2: omega.
subst m'''.
rewrite ?upd_Znth_upd_nth ?Znth_nth ; try omega.
rewrite /sub_step /subst_0xffffc.
rewrite Reduce.Zshiftr_div_pow2_16.
change (two_p 16) with (2^16).
reflexivity.
Qed.

Lemma verif_pack25519_8:
forall t' : list ℤ,
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
Zlength (mVI64 t') = 16 ->
forall mi1 : ℤ,
Int64.min_signed <=
Znth 15 t' 0 - 32767 -
Int64.signed (Int64.and (Int64.shr (Int64.repr mi1) (Int64.repr 16)) (Int64.repr 1)) <= Int64.max_signed /\
Int64.min_signed <= Int64.signed (Int64.repr (Znth 15 t' 0)) - 32767 <= Int64.max_signed.
Proof.
intros.
assert(0 <= Z.land (Z.shiftr (Int64.signed (Int64.repr mi1)) (Int64.unsigned (Int64.repr 16))) 1 <= 1).
apply and_0_or_1.
rewrite and64_repr.
assert(HZland: Z.land (Z.shiftr (Int64.signed (Int64.repr mi1)) (Int64.unsigned (Int64.repr 16))) 1 = 0 \/
  Z.land (Z.shiftr (Int64.signed (Int64.repr mi1)) (Int64.unsigned (Int64.repr 16))) 1 = 1) by omega.
destruct HZland as [HZland | HZland]; rewrite HZland.
1,2: assert(Int64.min_signed + 32767 <= Znth 15 t' 0 <= Int64.max_signed  + 32767).
2,4: repeat rewrite Int64.signed_repr.
2,6: split.
all: try solve[apply Forall_Znth ; [omega|]; eapply list.Forall_impl ; [eassumption |];
intros x Hx ; simpl in Hx ; solve_bounds_by_values].
all: solve_bounds_by_values.
Qed.

(* Lemma verif_pack25519_9:
forall j : ℤ,
0 <= j < 2 ->
forall t' : list ℤ,
forall m' : list ℤ,
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
Zlength m' = 16 ->
forall m'' : list ℤ,
m'' = upd_Znth 0 m' (Znth 0 t' 0 - 65517) ->
forall m''' : list ℤ,
m''' = sub_fn_rev 1 sub_step 15 m'' t' ->
Zlength m''' = 16
-> Int64.min_signed <= Znth 14 m''' 0 <= Int64.max_signed.
Proof.
intros.
repeat match goal with
  | [ H: context[Znth] |- _ ]=> rewrite Znth_nth in H
  | [ |- context[Znth] ]=> rewrite Znth_nth
  | _ => omega
end.
match goal with | [ |- context[nth ?a ?b ?c]] => replace (nth a b c) with (nth a b 0) end.
match goal with | [ H: context[nth ?a ?b ?c] |- _ ] => replace (nth a b c) with (nth a b 0) in H end.
2,3: apply nth_indep.
2,3: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2,3: rewrite /nat_of_Z ; apply Z2Nat.inj_lt ; rewrite -?Zlength_correct ; omega.
subst m''' m''.
rewrite ?Znth_nth ?upd_Znth_upd_nth ; try omega.
assert(Hbt: - 2 ^ 16 <= nth (Z.to_nat (15 - 1)) (sub_fn_rev 1 sub_step 15 (upd_nth 0 m' (subst_0xffed (nth 0 t' 0))) t') 0 <
   2 ^ 16).
apply sub_fn_rev_f_bound_nth ; try assumption ; omega.
move: Hbt.
Grind_add_Z ; rewrite /nat_of_Z /subst_0xffed; repeat change_Z_to_nat.
intros Hbt.
match goal with | [ |- _ <= ?a <= _ ] => remember a as blabla end.
solve_bounds_by_values.
Qed. *)

Lemma verif_pack25519_10:
forall msub15,
Int64.min_signed <=
1 - Int64.signed (Int64.and (Int64.shr (Int64.repr msub15) (Int64.repr 16)) (Int64.repr 1)) <= Int64.max_signed.
Proof.
intros.
rewrite and64_repr.
remember (Z.shiftr (Int64.signed (Int64.repr msub15)) (Int64.unsigned (Int64.repr 16))) as mi2.
assert(0 <= Z.land mi2 1 <= 1).
apply and_0_or_1.
assert(HZland: Z.land mi2 1 = 0 \/ Z.land mi2 1 = 1) by omega.
destruct HZland as [HZland | HZland]; rewrite HZland.
1,2: rewrite Int64.signed_repr ; solve_bounds_by_values.
Qed.

Lemma verif_pack25519_11:
forall t' : list ℤ,
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
forall m''' : list ℤ,
Zlength m''' = 16 ->
forall msub : list ℤ,
msub =
upd_Znth 14 (upd_Znth 15 m''' (Znth 15 t' 0 - 32767 - Z.land (Znth 14 m''' 0 / two_p 16) 1))
  (Z.land (Znth 14 m''' 0) 65535) ->
0 <= 15 < Zlength msub ->
0 <= 15 < Zlength (map Int64.repr msub) ->
forall msub15 : ℤ,
msub15 = Znth 15 msub 0 ->
1 - Z.land (Znth 15 msub 0 / two_p 16) 1 =
Int.signed (Int.repr 1) -
Z.land (Int64.signed (Int64.repr msub15) / two_p (Int64.unsigned (Int64.repr (Int.unsigned (Int.repr 16)))))
  (Int.signed (Int.repr 1)).
Proof.
intros.
assert(0 <= Z.land (Znth 14 m''' 0 / two_p 16) 1 <= 1) by apply and_0_or_1.
assert(HZland: Z.land (Znth 14 m''' 0 / two_p 16) 1 = 0 \/ Z.land (Znth 14 m''' 0 / two_p 16) 1 = 1) by omega.
assert(Int64.min_signed + 32767 <= Znth 15 t' 0 <= Int64.max_signed  + 32767) by solve_bounds_by_values_Znth.
assert(Int64.min_signed + 32768 <= Znth 15 t' 0 <= Int64.max_signed  + 32768) by solve_bounds_by_values_Znth.
all: subst msub msub15.
rewrite upd_Znth_diff ?upd_Znth_Zlength ; try omega.
rewrite upd_Znth_same ; try omega.
rewrite ?Int.signed_repr ?Int.unsigned_repr ?Int64.signed_repr ?Int64.unsigned_repr.
reflexivity.
all: destruct HZland as [HZland | HZland]; rewrite ?HZland.
all: solve_bounds_by_values.
Qed.

(* Lemma verif_pack25519_12:
forall t : list ℤ,
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t ->
Zlength t = 16 ->
forall j : ℤ,
0 <= j < 2 ->
forall t' : list ℤ,
t' = get_t (subst_select select_m_t j nil16 t) ->
forall m' : list ℤ,
m' = get_m (subst_select select_m_t j nil16 t) ->
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
Zlength m' = 16 ->
j >= 0 ->
forall m'' : list ℤ,
m'' = upd_Znth 0 m' (Znth 0 t' 0 - 65517) ->
Zlength m'' = 16 ->
forall m''' : list ℤ,
m''' = sub_fn_rev 1 sub_step 15 m'' t' ->
Zlength m''' = 16 ->
15 >= 1 ->
forall msub : list ℤ,
msub =
upd_Znth 14 (upd_Znth 15 m''' (Znth 15 t' 0 - 32767 - Z.land (Znth 14 m''' 0 / two_p 16) 1))
  (Z.land (Znth 14 m''' 0) 65535) ->
0 <= 15 < Zlength msub ->
0 <= 15 < Zlength (map Int64.repr msub) ->
forall msub15 : ℤ,
msub15 = Znth 15 msub 0 ->
forall b' : ℤ,
b' = 1 - Z.land (Znth 15 msub 0 / two_p 16) 1 ->
get_m (subst_select select_m_t (j + 1) nil16 t) = Sel25519 b' msub t'.
Proof.
intros.
rewrite subst_select_n.
2: omega.
subst msub m''' m'' m' b' t'.
replace (j + 1 - 1) with j.
2: omega.
remember (get_m (subst_select select_m_t j nil16 t)) as m'.
remember (get_t (subst_select select_m_t j nil16 t)) as t'.
rewrite /select_m_t /get_m /get_t.
rewrite /GetBit_pack25519.getbit_25519.
rewrite Z.shiftr_div_pow2.
2: omega.
rewrite ?upd_Znth_upd_nth ?Znth_nth /nat_of_Z ; try omega.
repeat change_Z_to_nat.
rewrite /m_from_t /subst_0xffed /mod0xffff /subst_0x7fffc.
match goal with | [ |- context[nth ?a ?b 0]] => replace (nth a b 0) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct.
2: rewrite upd_nth_Zlength.
2,3: rewrite upd_nth_Zlength sub_fn_rev_Zlength.
all: try rewrite upd_nth_Zlength.
2: change 15%nat with (Z.to_nat 15).
2: rewrite /nat_of_Z ; apply Z2Nat.inj_lt ; rewrite -?Zlength_correct ; omega.
all: change_Z_of_nat ; try omega.
match goal with | [ |- context[nth ?a ?b 0]] => replace (nth a b 0) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct H4 ; change_Z_to_nat ; omega.
match goal with | [ |- context[nth ?a ?b Inhabitant_Z]] => replace (nth a b Inhabitant_Z) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct H4 ; change_Z_to_nat ; omega.
match goal with | [ |- context[nth ?a ?b Inhabitant_Z]] => replace (nth a b Inhabitant_Z) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct sub_fn_rev_Zlength ?upd_nth_Zlength.
2: change 14%nat with (Z.to_nat 14).
2: rewrite /nat_of_Z ; apply Z2Nat.inj_lt ; rewrite -?Zlength_correct ; omega.
all: change_Z_of_nat ; try omega.
remember (sub_fn_rev 1 sub_step 15 (upd_nth 0 m' (nth 0 t' 0 - 65517)) t') as tttt0.

rewrite ?Int64.Zshiftr_div_two_p.
2: try omega.
assert(Zlength tttt0 = 16).
  subst tttt0; rewrite sub_fn_rev_Zlength ?upd_nth_Zlength ; change_Z_of_nat ; omega.
change (two_p 16) with (2^16).
rewrite upd_nth_diff_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_same_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_diff_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_diff_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_same_Zlength.
all: change_Z_of_nat ; try omega.
reflexivity.
Qed.
 *)
(* 
Lemma verif_pack25519_13:
forall t : list ℤ,
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t ->
Zlength t = 16 ->
forall j : ℤ,
0 <= j < 2 ->
forall t' : list ℤ,
t' = get_t (subst_select select_m_t j nil16 t) ->
forall m' : list ℤ,
m' = get_m (subst_select select_m_t j nil16 t) ->
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
Zlength m' = 16 ->
j >= 0 ->
forall m'' : list ℤ,
m'' = upd_Znth 0 m' (Znth 0 t' - 65517) ->
Zlength m'' = 16 ->
forall m''' : list ℤ,
m''' = sub_fn_rev 1 sub_step 15 m'' t' ->
Zlength m''' = 16 ->
15 >= 1 ->
forall msub : list ℤ,
msub =
upd_Znth 14 (upd_Znth 15 m''' (Znth 15 t' - 32767 - Z.land (Znth 14 m''' / two_p 16) 1))
  (Z.land (Znth 14 m''') 65535) ->
0 <= 15 < Zlength msub ->
0 <= 15 < Zlength (map Int64.repr msub) ->
forall msub15 : ℤ,
msub15 = Znth 15 msub ->
forall b' : ℤ,
b' = 1 - Z.land (Znth 15 msub / two_p 16) 1 ->
get_t (subst_select select_m_t (j + 1) nil16 t) = Sel25519 b' t' msub.
Proof.
intros.
rewrite subst_select_n.
2: omega.
subst msub m''' m'' m' b' t'.
replace (j + 1 - 1) with j.
2: omega.
remember (get_m (subst_select select_m_t j nil16 t)) as m'.
remember (get_t (subst_select select_m_t j nil16 t)) as t'.
rewrite /select_m_t /get_m /get_t.
rewrite /GetBit_pack25519.getbit_25519.
rewrite Z.shiftr_div_pow2.
2: omega.
rewrite ?upd_Znth_upd_nth ?Znth_nth /nat_of_Z ; try omega.
repeat change_Z_to_nat.
rewrite /m_from_t /subst_0xffed /mod0xffff /subst_0x7fffc.
match goal with | [ |- context[nth ?a ?b Inhabitant_Z]] => replace (nth a b Inhabitant_Z) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct.
2: rewrite upd_nth_Zlength.
2,3: rewrite upd_nth_Zlength sub_fn_rev_Zlength.
all: try rewrite upd_nth_Zlength.
2: change 15%nat with (Z.to_nat 15).
2: rewrite /nat_of_Z ; apply Z2Nat.inj_lt ; rewrite -?Zlength_correct ; omega.
all: change_Z_of_nat ; try omega.
match goal with | [ |- context[nth ?a ?b Inhabitant_Z]] => replace (nth a b Inhabitant_Z) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct H4 ; change_Z_to_nat ; omega.
match goal with | [ |- context[nth ?a ?b Inhabitant_Z]] => replace (nth a b Inhabitant_Z) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct H4 ; change_Z_to_nat ; omega.
match goal with | [ |- context[nth ?a ?b Inhabitant_Z]] => replace (nth a b Inhabitant_Z) with (nth a b 0) end.
2: apply nth_indep.
2: match goal with | [ |- (_ < ?A)%nat ] => rewrite -(Nat2Z.id A) end.
2: rewrite -Zlength_correct sub_fn_rev_Zlength ?upd_nth_Zlength.
2: change 14%nat with (Z.to_nat 14).
2: rewrite /nat_of_Z ; apply Z2Nat.inj_lt ; rewrite -?Zlength_correct ; omega.
all: change_Z_of_nat ; try omega.
remember (sub_fn_rev 1 sub_step 15 (upd_nth 0 m' (nth 0 t' 0 - 65517)) t') as tttt0.

rewrite ?Int64.Zshiftr_div_two_p.
2: try omega.
assert(Zlength tttt0 = 16).
  subst tttt0; rewrite sub_fn_rev_Zlength ?upd_nth_Zlength ; change_Z_of_nat ; omega.
change (two_p 16) with (2^16).
rewrite upd_nth_diff_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_same_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_diff_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_diff_Zlength ?upd_nth_Zlength.
all: change_Z_of_nat ; try omega.
rewrite upd_nth_same_Zlength.
all: change_Z_of_nat ; try omega.
reflexivity.
Qed. *)

(* Lemma verif_pack25519_14:
forall (o : list val),
Zlength o = 32 ->
forall t : list ℤ,
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t ->
Zlength t = 16 ->
forall t' : list ℤ,
t' = get_t (subst_select select_m_t 2 nil16 t) ->
Zlength t' = 16 ->
Forall (fun x : ℤ => 0 <= x < 2 ^ 16) t' ->
forall i : ℤ,
0 <= i < 16 ->
i >= 0 ->
firstn (nat_of_Z (2 * (i + 1))) (mVI (pack_for 8 t')) ++ skipn (nat_of_Z (2 * (i + 1))) o =
upd_Znth (2 * i + 1)
  (upd_Znth (2 * i) (firstn (nat_of_Z (2 * i)) (mVI (pack_for 8 t')) ++ skipn (nat_of_Z (2 * i)) o)
     (Vint
        (Int.zero_ext 8
           (Int.repr
              (Int64.unsigned (Int64.and (Int64.repr (Znth i t')) (Int64.repr (Int.signed (Int.repr 255)))))))))
  (Vint
     (Int.zero_ext 8
        (Int.repr (Int64.unsigned (Int64.shr (Int64.repr (Znth i t')) (Int64.repr (Int.unsigned (Int.repr 8)))))))).
Proof.
  intros.
  rewrite (Int.signed_repr 255).
  2: solve_bounds_by_values.
  rewrite (and64_repr _ 255).
  rewrite ?Int.zero_ext_and ; try omega.
  rewrite and_repr and_repr.
  rewrite Int64.shr_div_two_p.
  rewrite (Int64.signed_repr (Znth i t')).
  2: apply Forall_Znth ; [omega| solve_bounds_by_values_Forall_impl].
  rewrite (Int64.unsigned_repr 8).
  2: solve_bounds_by_values.
  rewrite Int64.unsigned_repr.
  2:{
  split.
  apply Z.land_nonneg ; by right.
  rewrite (Z.land_ones _ 8) ; [|omega].
  assert(2 ^ 8 < Int64.max_unsigned).
  solve_bounds_by_values.
  assert(Znth i t' mod 2 ^ 8 < 2 ^ 8).
  apply Z.mod_pos_bound.
  solve_bounds_by_values.
  omega.
  }
  rewrite (Int64.unsigned_repr (Znth i t' / two_p 8)).
  2:{
  split.
  apply Z_div_pos.
  change (two_p 8) with 256 ; omega.
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  assert(Znth i t' / two_p 8 <= 2^16 / two_p 8).
  apply Z_div_le.
  change (two_p 8) with 256 ; omega.
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  assert(2 ^ 16 / two_p 8 <= Int64.max_unsigned).
  change (two_p 8) with 256 ; solve_bounds_by_values.
  compute ; intros ; discriminate.
  omega.
  }
  remember (mVI (pack_for 8 t')) as r'.
  replace (Vint (Int.repr (Z.land (Z.land (Znth i t') 255) (two_p 8 - 1)))) with (Znth (2*i) r').
  rewrite -(upd_Znth_app_step_Zlength (2*i) r' o) ; try omega.
  2: subst r' ; rewrite Zlength_map Zlength_map  pack_for_Zlength_32_16 ; omega.
  replace (2 * (i + 1)) with ((2 * i + 1) + 1) by omega.
  orewrite simple_S_i.
  rewrite (upd_Znth_app_step_Zlength (2 * i + 1) r' o) ; try omega.
  2: subst r' ; rewrite Zlength_map Zlength_map pack_for_Zlength_32_16 ; omega.
  change (Z.to_nat (2 * i + 1)) with (nat_of_Z (2 * i + 1)).
  rewrite simple_S_i /nat_of_Z ; try omega.
  f_equal.
  {
  subst r'.
  rewrite Znth_map.
  2: rewrite Zlength_map pack_for_Zlength_32_16 ; omega.
  rewrite Znth_map.
  2: rewrite pack_for_Zlength_32_16 ; omega.
  f_equal.
  f_equal.
  rewrite ?Znth_nth ; try omega.
  replace (nat_of_Z (2 * i + 1)) with (2 * nat_of_Z i + 1)%nat.
  2:{
  rewrite nat_of_Z_plus ; try omega.
  rewrite /nat_of_Z.
  rewrite Z2Nat.inj_mul ; try omega.
  reflexivity.
  }
  rewrite pack_for_nth_o.
  change (two_p 8 - 1) with (Z.ones 8).
  rewrite Z.land_ones.
  rewrite Z.mod_small.
  reflexivity.
  2: omega.
  rewrite -Znth_nth ; try omega.
  split.
  apply Z_div_pos.
  change (two_p 8) with 256 ; omega.
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  apply Zdiv_lt_upper_bound.
  change (two_p 8) with 256 ; solve_bounds_by_values.
  change (2 ^ 8 * two_p 8) with (2^16).
  apply Forall_Znth.
  omega.
  solve_bounds_by_values_Forall_impl.
  }
  subst r'.
  rewrite Znth_map.
  2: rewrite Zlength_map pack_for_Zlength_32_16 ; omega.
  rewrite Znth_map.
  2: rewrite pack_for_Zlength_32_16 ; omega.
  f_equal.
  f_equal.
  rewrite ?Znth_nth ; try omega.
  replace (nat_of_Z (2 * i)) with (2 * nat_of_Z i)%nat.
  2:{
  rewrite /nat_of_Z.
  rewrite Z2Nat.inj_mul ; try omega.
  reflexivity.
  }
  rewrite pack_for_nth_e.
  change (two_p 8 - 1) with (Z.ones 8).
  change (255) with (Z.ones 8).
  rewrite Z.land_ones ; try omega.
  rewrite Z.land_ones ; try omega.
  rewrite Z.mod_mod ; solve_bounds_by_values.
  f_equal.
Qed. *)

Close Scope Z.