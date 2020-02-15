Set Warnings "-notation-overridden,-parsing".
From Tweetnacl_verif Require Import init_tweetnacl.
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


Close Scope Z.