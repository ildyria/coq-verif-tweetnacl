Require Import Coq.ZArith.BinInt.
Require Import Tools.
Require Import List.
Require Import Coq.Classes.RelationClasses.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Import ListNotations.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint sum_list_Z (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (Z.add h1 h2) :: sum_list_Z q1 q2
end.

Fixpoint sum_list_Z_n (n:nat) (a b : list Z) : list Z := match n, a, b with 
  | 0, _, _ => []
  | S p, [], []  => []
  | S p, [], h::q  => h :: (sum_list_Z_n p [] q)
  | S p, h::q, []  => h :: (sum_list_Z_n p [] q)
  | S p, h1::q1, h2::q2 => (Z.add h1 h2) :: (sum_list_Z_n p q1 q2)
end.

Lemma sum_list_Z_empty1: forall h q, sum_list_Z (h :: q) [] = h :: sum_list_Z q [].
Proof.
induction q ; go.
Qed.

Lemma sum_list_Z_empty2: forall h q, sum_list_Z [] (h :: q) = h :: sum_list_Z [] q.
Proof.
induction q ; go.
Qed.

Lemma sum_list_Z_empty3: forall h q, sum_list_Z (h :: q) [] = h :: sum_list_Z [] q.
Proof.
induction q ; go.
Qed.

Lemma sum_list_eq: forall n a b, length a <= n -> length b <= n -> sum_list_Z a b = sum_list_Z_n n a b.
Proof.
induction n.
destruct a, b ; go.
intros a b Hla Hlb.
destruct a, b ; go.
rewrite sum_list_Z_empty2 ; unfold sum_list_Z_n ; fold sum_list_Z_n; f_equal ; apply IHn ; go.
simpl in Hla ; apply le_S_n in Hla.
rewrite sum_list_Z_empty3 ; unfold sum_list_Z_n ; fold sum_list_Z_n; f_equal ; apply IHn; go.
simpl in Hla, Hlb ; apply le_S_n in Hla ; apply le_S_n in Hlb.
simpl ; f_equal ; apply IHn ; go.
Qed.

Lemma sum_sliced: forall n a b, slice n (sum_list_Z a b) = sum_list_Z_n n a b.
Proof.
induction n ; intros a b ; simpl ; flatten ; try inv Eq ; rewrite <- IHn ; go.
Qed.

Open Scope Z.

Section FiniteFied.

Variable n:Z.
Hypothesis Hn: n > 0.

Lemma addition: forall a b : Z,
  a < 2^n ->
  b < 2^n ->
  a + b < 2^Z.succ n.
Proof.
intros a b Ha Hb.
assert(2 ^ Z.succ n = 2 * 2 ^ n).
{
(*  SearchAbout Z.pow.*)
  apply Z.pow_succ_r.
  omega.
}
rewrite H.
omega.
Qed.

(* By J-M Madiot *)
Lemma addition': forall a b : Z, a < 2^63 -> b < 2^63 -> a + b < 2^64.
Proof.
change (2 ^ 64) with (2 ^ 63 * 2).
intros; omega.
Qed.

Fixpoint ToFFi (a: list Z) (i:Z) := match a with 
| [] => 0
| h :: q => h * Z.pow 2 (n * i) + ToFFi q (Z.succ i)
end.

Fixpoint ToFF (a : list Z) := match a with 
| [] => 0
| h :: q => h + Z.pow 2 n * ToFF q
end.

Lemma pown: 2 ^ n > 1.
Proof.
rewrite Z.gt_lt_iff.
apply Z.pow_gt_1 ; try omega.
Qed.

Lemma pown0: 2 ^ n > 0.
Proof.
assert(Hp:= pown).
omega.
Qed.

Lemma ToFFeq : forall l i, i >= 0 -> ToFFi l i = Z.pow 2 (n * i) * ToFF l.
Proof.
dependent induction l; go.
intros i Hi.
unfold ToFFi ; fold ToFFi.
unfold ToFF ; fold ToFF.
assert (H := Hi).
apply IHl in H.
rewrite <- Zred_factor4.
rewrite Z.mul_comm.
f_equal.
(* SearchAbout Z.mul. *)
rewrite <- Zmult_assoc_reverse.
(* SearchAbout Z.pow. *)
rewrite <- Zpower_exp ; go ; try omega.
(* SearchAbout Z.mul. *)
rewrite Zmult_succ_r_reverse.
go.
apply Z.ge_le_iff.
rewrite Zmult_comm.
apply Zmult_gt_0_le_0_compat ; omega.
Qed.


Corollary ToFFeqD : forall l, ToFFi l 0 = ToFF l.
Proof.
intro l.
assert (Z.pow 2 (n * 0) = 1) by (rewrite <- Zmult_0_r_reverse ; go).
assert (ToFF l = Z.pow 2 (n * 0) * ToFF l).
rewrite H.
rewrite Z.mul_comm ; go.
rewrite H0.
apply ToFFeq.
omega.
Qed.

Lemma ToFFnil : ToFF nil = 0.
Proof.
go.
Qed.

Lemma ToFFiApp : forall a b, ToFF (a ++ b) = ToFF a + Z.pow 2 (n * Z.of_nat (length a)) * ToFF b.
Proof.
induction a as [| h a Hl].
- intro b.
rewrite ToFFnil.
assert ([] ++ b = b) by apply app_nill_l. rewrite H ; go ; clear H.
assert (Z.of_nat (length (nil:(list Z))) = 0) by go. rewrite H ; go ; clear H.
rewrite <- Zmult_0_r_reverse.
rewrite Z.pow_0_r.
omega.
- intro b.
assert ((h::a) ++ b = h :: a ++ b) by apply consApp2 ; rewrite H ; clear H.
unfold ToFF; fold ToFF.
rewrite Hl.
rewrite Zplus_assoc_reverse.
f_equal.
rewrite <- Zred_factor4.
f_equal.
rewrite <- Zmult_assoc_reverse.
assert(Z.of_nat (length (h :: a)) = Z.of_nat (1 + length a)) by go ; rewrite H ; clear H.
rewrite Nat2Z.inj_add.
assert(Z.of_nat 1 = 1) by go ; rewrite H ; clear H.
rewrite <- Zred_factor4.
rewrite Z.pow_add_r ; try omega.
assert(n * 1 = n) by go ; rewrite H ; clear H.
go.
rewrite Z.mul_comm.
apply Zmult_gt_0_le_0_compat ; omega.
Qed.

Lemma sumListToFF : forall a b o, sum_list_Z a b = o -> ToFF a + ToFF b = ToFF o.
Proof.
induction a , b.
- intros o HSum ; go.
- intros o HSum ; go.
- intros o HSum ; go.
- intros o HSum.
  destruct o ; go.
  simpl in HSum.
  assert(Hh:= HSum).
  apply headSame in Hh.
  apply tailSame in HSum.
  apply IHa in HSum.
  unfold ToFF; fold ToFF.
  rewrite <- Z.add_shuffle2.
  rewrite Zred_factor4.
  apply Zplus_eq_compat.
  apply Hh.
  f_equal.
  rewrite Z.add_comm.
  apply HSum.
Qed.

Corollary sumListToFF2: forall a b, ToFF (sum_list_Z a b) = ToFF a + ToFF b.
Proof.
intros a b.
assert(exists o, o = sum_list_Z a b) by (exists (sum_list_Z a b) ; go) ; destruct H.
symmetry; subst x ; apply sumListToFF ; go.
Qed.

Definition getCarry m :=  Z.shiftr m n.

(* Compute (getCarry (Z.pow 2 18)). *)

Definition getResidute m := m mod (Z.pow 2 n).

Lemma withinBounds16 : forall m, getResidute m < Z.pow 2 n.
Proof.
intro m.
unfold getResidute.
SearchAbout Z.modulo.
apply Z_mod_lt.
apply pown0.
Qed.

Lemma residuteCarry : forall m, getResidute m + Z.pow 2 n *getCarry m = m.
Proof.
intro m.
unfold getResidute.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega.
rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq.
apply pown0.
Qed.

Lemma getCarryMonotone : forall m, m > 0 -> getCarry m < m.
Proof.
intros m Hm.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega.
induction m ; go.
- apply Z_div_lt ; go.
assert(2 = 2 ^ 1) by go.
rewrite{2} H ; clear H.
rewrite Z.ge_le_iff.
apply Z.pow_le_mono_r_iff ; omega.
- assert (Z.neg p < 0) by apply Zlt_neg_0 ; go.
Qed.


Fixpoint Carrying a (l:list Z) := match a,l with 
| 0,[] => []
| a,[] => [a]
| a,h :: q => getResidute (a + h) :: Carrying (getCarry (a + h)) q
end.

Lemma CarryPreserveConst : forall l a , a + ToFF l  = ToFF (Carrying a l).
Proof.
induction l as [| h q IHl].
intro a ; destruct a ; assert(Hn0: 2 ^ n * 0 = 0) by (symmetry ; apply Zmult_0_r_reverse) ; simpl ; try rewrite Hn0 ; go.
intro a.
unfold Carrying ; fold Carrying.
flatten ;
unfold ToFF ; fold ToFF ; rewrite <- IHl ;
rewrite <- Zplus_assoc_reverse ; 
rewrite <- Zred_factor4 ;
rewrite <- Zplus_assoc_reverse ;
rewrite residuteCarry ;
reflexivity.
Qed.

Corollary CarryPreserve : forall l, ToFF l = ToFF (Carrying 0 l).
Proof.
intros.
assert(H: ToFF l = 0 + ToFF l) by go.
rewrite H ; clear H.
apply CarryPreserveConst.
Qed.

End FiniteFied.

Compute Z.pow 2 256 mod (Z.pow 2 255 - 19).
Lemma t2256is38 : Z.pow 2 256 mod (Z.pow 2 255 - 19) = 38 mod (Z.pow 2 255 - 19).
Proof.
compute.
go.
(*
change 38 with (2 * 19).
change 256 with (Z.succ 255).
rewrite Z.pow_succ_r ; try omega.
rewrite <- Zmult_mod_idemp_r.
symmetry.
rewrite <- Zmult_mod_idemp_r.
f_equal.*)

Qed.

Definition reduce n := 
  let c := n / 2^(256) in
  n + 38 * c - 2^(256) * c.

Lemma reduceFF : forall m, (reduce m) mod (2^255 - 19) = m mod (2^255 - 19).
Proof.
intro m.
unfold reduce.
rewrite <- Zminus_mod_idemp_r.
rewrite <- Zminus_mod_idemp_l.
rewrite <- Zplus_mod_idemp_r.
rewrite <- Zmult_mod_idemp_l.
rewrite <- t2256is38.
rewrite <- Zplus_mod_idemp_l.
rewrite Zminus_mod_idemp_l.
rewrite Zmult_mod_idemp_l.
rewrite <- Z.add_sub_assoc.
rewrite <- Zminus_diag_reverse.
rewrite <- Zplus_0_r_reverse.
rewrite Zmod_mod.
reflexivity.
Qed.




