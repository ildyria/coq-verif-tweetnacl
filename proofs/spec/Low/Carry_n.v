Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.Reduce.

Local Open Scope Z.
Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.


Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Fixpoint Carrying_n (p:nat) (a:Z) (l:list Z) : list Z := match p,a,l with
| _,  0,[]     => []
| _,  a,[]     => [a]
| 0%nat,  a,h::q   => (h + a) :: q
| S p,a,h :: q => getResidue n (h + a) :: Carrying_n p (getCarry n (h + a)) q
end.

Lemma Carry_n_step: forall m a h q, Carrying_n (S m) a (h :: q) = getResidue n (h + a) :: Carrying_n m (getCarry n (h + a)) q.
Proof. intros; simpl ; flatten. Qed.

Lemma Carry_n_step2: forall m a h q, Carrying_n (S m) a (h :: q) = getResidue n (a + h) :: Carrying_n m (getCarry n (a + h)) q.
Proof. intros; simpl ; replace (h + a) with (a + h) by omega ; flatten. Qed.

Lemma Carry_n_step_0 : forall h q a, Carrying_n 0 a (h :: q) = (h + a) :: q.
Proof. intros ; simpl; flatten. Qed.

Lemma Carry_n_step_02 : forall h q a, Carrying_n 0 a (h :: q) = (a + h) :: q.
Proof. intros ; simpl ; replace (h + a) with (a + h) by omega ; flatten. Qed.

Lemma Carrying_n_length: forall l (m:nat) a, (m < length l)%nat -> length (Carrying_n m a l) = length l.
Proof. induction l as [|h q IHl]; intros [] a Hm; simpl ; flatten ; go. Qed.

Lemma Carrying_n_Zlength: forall l (m:nat) a, m < length l -> Zlength (Carrying_n m a l) = Zlength l.
Proof. convert_length_to_Zlength Carrying_n_length. Qed.

Lemma CarrynPreserveConst : forall m l a , a + (ℤ.lst l)  = ℤ.lst Carrying_n m a l.
Proof.
  assert(Hn0: 2 ^ n * 0 = 0) by (symmetry ; apply Zmult_0_r_reverse).
  induction m ; intros l a.
  - simpl ; flatten ; try rewrite <- ZofList_add ; go.
  - simpl ; flatten ; go ;
    rewrite! ZofList_cons ;
    rewrite <- IHm ; 
    rewrite <- Zplus_assoc_reverse ; 
    rewrite <- Zred_factor4 ;
    rewrite <- Zplus_assoc_reverse ;
    rewrite residuteCarry ; go.
Qed.

Corollary CarrynPreserve : forall m l, ℤ.lst l = ℤ.lst Carrying_n m 0 l.
Proof.
  intros.
  simpl.
  rewrite -CarrynPreserveConst.
  omega.
Qed.

End Integer.

Theorem Zcarry_n_bounds_length:
  forall l,
    length l = 16%nat ->
    Forall (fun x => -2^62 < x < 2^62) l ->
    forall j, 0 <= j < 16 ->
    Forall (fun x => - 2^63 < x < 2^63) (Carrying_n 16 (Z.to_nat j) 0 l).
Proof.
  intros l H HForalll i Hi.
  apply (nth_Forall _ _ _ 0).
  intros j.
  assert(Hi': exists i', Z.to_nat i = i') by eauto.
  destruct Hi' as [i' Hi'].
    assert(Hi'': 0 <= i' < 16).
    subst ; rewrite Z2Nat.id ; omega.
  apply destruct_length_16 in H ; do 16 destruct H.
  rewrite Hi'.
  subst l.
  assert(Hi''': (i' = 0 \/ i' = 1 \/ i' = 2 \/ i' = 3 \/ i' = 4 \/ i' = 5 \/ i' = 6 \/ i' = 7 \/ i' = 8 \/ i' = 9 \/
       i' = 10 \/ i' = 11 \/ i' = 12 \/ i' = 13 \/ i' = 14 \/ i' = 15 \/ 15 < i')%nat) by omega.
  assert(H16 : 16 > 0) by reflexivity.
  assert(H216262: 2^16 < 2^63) by reflexivity.
  assert(H262263: 2^62 < 2^63) by reflexivity.
  assert(H263262: - 2^63 < - 2^62) by reflexivity.
  assert(H2630: - 2^63 < 0) by reflexivity.
  assert(i' = 0%nat ∨ i' = 1%nat ∨ i' = 2%nat ∨ i' = 3%nat ∨ i' = 4%nat ∨ i' = 5%nat ∨ i' = 6%nat ∨ i' = 7%nat ∨ i' = 8%nat ∨ i' = 9%nat ∨ i' = 10%nat ∨ i' = 11%nat ∨ i' = 12%nat ∨ i' = 13%nat ∨ i' = 14%nat ∨ i' = 15%nat) by omega.
  move: HForalll.
  rewrite ?Forall_cons => HForalll.
  repeat match goal with
    | [H : (_ /\ _) /\ _ |-_] => destruct H
  end.
  clear Hi Hi' i Hi''' H17.
  rename H into Hi'.
  assert(HH : forall k, 0 ≤ getResidue 16 k ∧ getResidue 16 k < 2 ^ 16) by (clear ; intro; eapply getResidue_bounds ; omega).
  repeat match goal with
    | _ => rewrite Carry_n_step
    | _ => rewrite Carry_n_step_0
    | [H : _ \/ _ |- _ ] => destruct H ; try subst i'
    | _ => unfold nth ; flatten ; try omega
  end;
  repeat match goal with
    | _ => omega
    | [ HH : context[getResidue] |- - 2 ^ 63 < getResidue 16 (?x) ∧ getResidue 16 (?x) < 2 ^ 63 ] => specialize HH with x
    | [ |- context[2 ^ 63] ] => change (-2^63) with ((-2^62) + (-2^62)); change (2^63) with ((2^62) + (2^62))
    | [ |- _ < _ ∧ _ < _ ] => apply Add_interval_mono
    | [ |- -2^62 < getCarry _ _ ∧ _ < _ ] => apply getCarry_bound_str63
  end.
Qed.
(* THIS QED IS REALLY SLOW... could be improved by reflection ... *)

Lemma Carry_n_length_False: forall (h:Z) (q:list Z), Carrying_n 16 15 0 (h :: q) = [] -> False.
Proof. intros ; rewrite Carry_n_step in H ; false. Qed.

Local Close Scope Z.

Lemma Carrying_n_1_nat : forall i o z m,
  nth (S i) (Carrying_n m i z o) 0 = nth (S i) o 0.
Proof.
  induction i as [|i iHi]; intros [| h q ] z m; simpl; flatten ; try reflexivity.
  all: simpl ; apply iHi; simpl in H ; omega.
Qed.

Local Open Scope Z.
Lemma Carrying_n_1 : forall i o z m,
  0 <= i ->
  nth (Z.to_nat (i + 1)) (Carrying_n m (Z.to_nat i) z o) 0 = nth (Z.to_nat (i + 1)) o 0.
Proof.
  intros.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  apply Carrying_n_1_nat.
  rewrite Z2Nat.inj_add ; try omega.
  change (Z.to_nat 1) with 1%nat.
  omega.
Qed.

Local Close Scope Z.