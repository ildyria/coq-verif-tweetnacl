Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Car.Reduce.
Require Import Tweetnacl.Op.M.

Require Import stdpp.prelude.

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
  symmetry.
  rewrite Zplus_0_r_reverse.
  symmetry.
  rewrite Z.add_comm.
  apply CarrynPreserveConst.
Qed.

End Integer.

(*




Theorem Zcar25519_bounds_length:
  forall l1 l2 l3,
    length l1 = 16%nat ->
    length l2 = 16%nat -> (* not required but easier *)
    length l3 = 16%nat -> (* not required but easier *)
    Forall (fun x => -2^62 < x < 2^62) l1 ->
    l2 = car25519 l1 ->
    l3 = car25519 l2 ->
    Forall (fun x => 0 <= x < 2^16) (car25519 l3).
Proof.
  intros l1 l2 l3 Hl1 Hl2 Hl3 HForalll1 Hcarr1 Hcarr2.
  apply Forall_lookup.
  intros i x Hl.
*)
Local Close Scope Z.
