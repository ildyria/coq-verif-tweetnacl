Require Export Coq.ZArith.BinInt.
Require Export List.
Require Export Tools.
Import ListNotations.

Open Scope Z.

Notation "ℤ.ℕ A" := (Z.of_nat A) (at level 60, right associativity).
Notation "A :𝓟" := (A mod (2^255 - 19)) (at level 80, right associativity).

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

Fixpoint ToFFi (a: list Z) (i:Z) : Z := match a with 
| [] => 0
| h :: q => h * Z.pow 2 (n * i) + ToFFi q (Z.succ i)
end.

Fixpoint ToFF (a : list Z) : Z := match a with 
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

Lemma ToFF_eq : forall l i, i >= 0 -> ToFFi l i = 2^(n * i) * ToFF l.
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


Corollary ToFF_eq_D : forall l, ToFFi l 0 = ToFF l.
Proof.
intro l.
assert (2^(n * 0) = 1) by (rewrite <- Zmult_0_r_reverse ; go).
assert (ToFF l = 2^(n * 0) * ToFF l).
rewrite H.
rewrite Z.mul_comm ; go.
rewrite H0.
apply ToFF_eq.
omega.
Qed.

Lemma ToFF_nil : ToFF nil = 0.
Proof.
go.
Qed.

Lemma ToFF_cons : forall a b, ToFF (a :: b) = a + 2^n * ToFF b.
Proof.
intros a b ; go.
Qed.


Lemma ToFF_app : forall a b, ToFF (a ++ b) = ToFF a + 2^(n * ℤ.ℕ (length a)) * ToFF b.
Proof.
induction a as [| h a Hl].
- intro b.
rewrite ToFF_nil.
assert ([] ++ b = b) by apply app_nill_l. rewrite H ; go ; clear H.
assert (ℤ.ℕ (length (nil:(list Z))) = 0) by go. rewrite H ; go ; clear H.
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
assert(ℤ.ℕ (length (h :: a)) = ℤ.ℕ (1 + length a)) by go ; rewrite H ; clear H.
rewrite Nat2Z.inj_add.
assert(ℤ.ℕ 1 = 1) by go ; rewrite H ; clear H.
rewrite <- Zred_factor4.
rewrite Z.pow_add_r ; try omega.
assert(n * 1 = n) by go ; rewrite H ; clear H.
go.
rewrite Z.mul_comm.
apply Zmult_gt_0_le_0_compat ; omega.
Qed.

Definition getCarry (m:Z) : Z :=  Z.shiftr m n.

(* Compute (getCarry (Z.pow 2 18)). *)

Definition getResidute (m:Z) : Z := m mod 2^n.

Lemma withinBounds16 : forall m:Z, getResidute m < 2^n.
Proof.
intro m.
unfold getResidute.
apply Z_mod_lt.
apply pown0.
Qed.

Lemma residuteCarry : forall m:Z, getResidute m + 2^n *getCarry m = m.
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
rewrite H at 2; clear H.
rewrite Z.ge_le_iff.
apply Z.pow_le_mono_r_iff ; omega.
- assert (Z.neg p < 0) by apply Zlt_neg_0 ; go.
Qed.


Fixpoint Carrying (a:Z) (l:list Z) : list Z := match a,l with 
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

Theorem ToFF_transitive: forall (f g:list Z -> list Z) f' g' l,
  (forall l, ToFF (g l) = g' (ToFF l)) ->
  (forall l, ToFF (f l) = f' (ToFF l )) -> 
  ToFF (f (g l)) = f' (g' (ToFF l)).
Proof.
go.
Qed.

Lemma ToFF_tail : forall l (m:nat),
  2^(n * ℤ.ℕ (length (slice m l))) * ToFF (tail m l) = ToFF l - ToFF (slice m l).
Proof.
intros l; destruct l; intros m.
simpl.
rewrite slice_length_le ; go.
rewrite tail_length_le ; go.
assert(HS: 2^(n * ℤ.ℕ (length (slice m (z::l)))) * ToFF (tail m (z :: l)) = 2^(n * ℤ.ℕ (length (slice m (z::l)))) * ToFF (tail m (z :: l)) - ToFF (slice m (z :: l)) + ToFF (slice m (z :: l))) by omega.
rewrite HS ; clear HS.
rewrite <- Z.add_sub_swap.
f_equal.
rewrite Z.add_comm.
rewrite <- ToFF_app ; go.
assert(HS: slice m (z :: l) ++ tail m (z :: l) = z :: l).
apply slice_tail_app.
rewrite HS ; clear HS.
go.
Qed.

Lemma ToFF_slice : forall l (m:nat),
  ToFF (slice m l) = ToFF l - 2^(n * ℤ.ℕ (length (slice m l))) * ToFF (tail m l).
Proof.
intros l m.
rewrite ToFF_tail.
omega.
Qed.

Lemma ToFF_slice_tail : forall l (m:nat),
  ToFF (slice m l) + 2^(n * ℤ.ℕ (length (slice m l))) * ToFF (tail m l) = ToFF l.
Proof.
intros l m.
rewrite ToFF_tail.
go.
Qed.

End FiniteFied.
