Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Low.Carry_n.

Local Open Scope Z.
Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.


Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Fixpoint Carrying (a:Z) (l:list Z) : list Z := match a,l with 
| 0,[] => []
| a,[] => [a]
| a,h :: q => getResidue n (a + h) :: Carrying (getCarry n (a + h)) q
end.

Lemma Carrying_n_eq: forall l (m:nat) a, m = length l -> Carrying_n n m a l = Carrying a l.
Proof.
  induction l as [|h q IHl]; intros m a Hm; go.
  destruct m.
  inv Hm.
  simpl in *.
  inversion Hm.
  replace (h + a) with (a + h) by omega.
  flatten ; f_equal ; go.
Qed.

Lemma Carrying_n_eq_Z: forall l (m:nat) a, Zlength l = m -> Carrying_n n m a l = Carrying a l.
Proof. convert_length_to_Zlength Carrying_n_eq. Qed.

Lemma CarryPreserveConst : forall l a , a + (ℤ.lst l) = ℤ.lst Carrying a l.
Proof.
  induction l as [| h q IHl].
  intro a ; destruct a ; assert(Hn0: 2 ^ n * 0 = 0) by (symmetry ; apply Zmult_0_r_reverse) ; simpl ; try rewrite Hn0 ; go.
  intro a ; unfold Carrying ; fold Carrying.
  flatten ;
  unfold ZofList ; fold ZofList ; rewrite <- IHl ;
  rewrite <- Zplus_assoc_reverse ; 
  rewrite <- Zred_factor4 ;
  rewrite <- Zplus_assoc_reverse ;
  rewrite residuteCarry ;
  go.
Qed.

Corollary CarryPreserve : forall l, ℤ.lst l = ℤ.lst Carrying 0 l.
Proof.
  intros.
  symmetry.
  rewrite -CarryPreserveConst.
  omega.
Qed.

End Integer.

Close Scope Z.
(* ADD LENGTH PROOF *)










