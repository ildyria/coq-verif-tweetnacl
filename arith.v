Require Import Coq.ZArith.BinInt.
Require Import Tools.
Require Import List.
Require Import Coq.Classes.RelationClasses.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.


Open Scope Z.

Lemma addition: forall n a b : Z,
  0 <= n ->
  a < 2^n ->
  b < 2^n ->
  a + b < 2^Z.succ n.
Proof.
intros n a b Hn Ha Hb.
assert(2 ^ Z.succ n = 2 * 2 ^ n).
{
(*  SearchAbout Z.pow.*)
  apply Z.pow_succ_r.
  auto.
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

Import ListNotations.

Fixpoint ToFFi (a: list Z) (i:Z) := match a with 
| [] => 0
| h :: q => h * Z.pow 2 (16 * i) + ToFFi q (Z.succ i)
end.

Fixpoint ToFF (a : list Z) := match a with 
| [] => 0
| h :: q => h + Z.pow 2 16 * ToFF q
end.

Hint Rewrite Zred_factor4.
Hint Rewrite Z.mul_comm.
Hint Resolve f_equal.
Hint Rewrite Zmult_assoc_reverse.
Hint Rewrite Zpower_exp.
Hint Rewrite Zmult_succ_r_reverse.

Lemma ToFFeq : forall l i, i >= 0 -> ToFFi l i = Z.pow 2 (16 * i) * ToFF l.
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
Qed.


Corollary ToFFeqD : forall l, ToFFi l 0 = ToFF l.
Proof.
intro l.
assert (Z.pow 2 (16 * 0) = 1) by go.
assert (ToFF l = Z.pow 2 (16 * 0) * ToFF l).
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

Lemma ToFFiApp : forall a b, ToFF (a ++ b) = ToFF a + Z.pow 2 (16 * Z.of_nat (length a)) * ToFF b.
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
assert(16 * 1 = 16) by go ; rewrite H ; clear H.
go.
Qed.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint sum_list_Z (a b : list Z) : list Z := match a,b with
| [], q => q
| q,[] => q
| h1::q1,h2::q2 => (h1 + h2) :: sum_list_Z q1 q2
end.

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

Definition getCarry n :=  Z.shiftr n 16.

(* Compute (getCarry (Z.pow 2 18)). *)

Definition getResidute n := n mod (Z.pow 2 16).

Lemma withinBounds16 : forall n, getResidute n < Z.pow 2 16.
Proof.
intro n.
unfold getResidute.
SearchAbout Z.modulo.
apply Z_mod_lt.
symmetry.
simpl.
reflexivity.
Qed.

Lemma residuteCarry : forall n, getResidute n + Z.pow 2 16 *getCarry n = n.
Proof.
intro n.
unfold getResidute.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega ; 
rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq ; symmetry ; auto.
Qed.

Lemma getCarryMonotone : forall n, n > 0 -> getCarry n < n.
Proof.
intros n Hn.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega.
induction n ; go.
apply Z_div_lt ; go.
assert(2 = 2 ^ 1) by go.
rewrite{2} H ; clear H.
rewrite Z.ge_le_iff.
apply Z.pow_le_mono_r_iff; go.
assert (Z.neg p < 0) by apply Zlt_neg_0.
go.
Qed.


Fixpoint Carrying a (l:list Z) := match a,l with 
| 0,[] => []
| a,[] => [a]
| a,h :: q => getResidute (a + h) :: Carrying (getCarry (a + h)) q
end.

Lemma CarryPreserveConst : forall l a , a + ToFF l  = ToFF (Carrying a l).
Proof.
induction l as [| h q IHl].
intro a ; destruct a ; go.
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

