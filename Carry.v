Require Export ZofList.
Require Export Reduce.
Import ListNotations.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Definition getCarry (m:Z) : Z :=  Z.shiftr m n.

(* Compute (getCarry (Z.pow 2 18)). *)

Definition getResidute (m:Z) : Z := m mod 2^n.

Lemma getResidute_0 : getResidute 0 = 0.
Proof.
go.
Qed.

Lemma getCarry_0 : getCarry 0 = 0.
Proof.
apply Z.shiftr_0_l.
Qed.

Lemma withinBounds16 : forall m:Z, getResidute m < 2^n.
Proof.
intro m.
unfold getResidute.
apply Z_mod_lt.
apply pown0.
assumption.
Qed.

Lemma residuteCarry : forall m:Z, getResidute m + 2^n *getCarry m = m.
Proof.
intro m.
unfold getResidute.
unfold getCarry.
rewrite Z.shiftr_div_pow2 ; try omega.
rewrite Z.add_comm ; symmetry ;apply Z_div_mod_eq.
apply pown0.
assumption.
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

Fixpoint Carrying_n (n:nat) (a:Z) (l:list Z) : list Z := match n,a,l with 
| _,  0,[]     => []
| _,  a,[]     => [a]
| 0%nat,  a,h::q   => (a + h) :: q
| S p,a,h :: q => getResidute (a + h) :: Carrying_n p (getCarry (a + h)) q
end.

Lemma Carry_n_step: forall m a h q, Carrying_n (S m) a (h :: q) = getResidute (a + h) :: Carrying_n m (getCarry (a + h)) q.
Proof.
intros.
simpl.
flatten.
Qed.

Lemma Carrying_n_eq: forall l (m:nat) a, m = length l -> Carrying_n m a l = Carrying a l.
Proof.
induction l as [|h q IHl]; intros m a Hm; go.
destruct m.
inv Hm.
simpl in *.
inversion Hm.
flatten ; f_equal ; go.
Qed.

Lemma Carrying_n_length: forall l (m:nat) a, (m < length l)%nat -> length (Carrying_n m a l) = length l.
Proof.
induction l as [|h q IHl]; intros [] a Hm; simpl ; flatten ; go.
Qed.


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
reflexivity.
Qed.

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

Corollary CarryPreserve : forall l, ℤ.lst l = ℤ.lst Carrying 0 l.
Proof.
intros.
replace (ℤ.lst l) with (0 + ℤ.lst l) by go.
apply CarryPreserveConst.
Qed.

Corollary CarrynPreserve : forall m l, ℤ.lst l = ℤ.lst Carrying_n m 0 l.
Proof.
intros.
replace (ℤ.lst l) with (0 + ℤ.lst l) by go.
apply CarrynPreserveConst.
Qed.

End Integer.

Definition backCarry (l:list Z) : (list Z) := 
  match l with
  | [] => []
  | h :: q => let v := nth 15 l 0 in
              (h + 38 * getCarry 16 v) :: slice 14 q ++ [getResidute 16 v]
  end.

Lemma backCarry_ToFF_25519 : forall l, (length l <= 16)%nat -> (ℤ16.lst l) :𝓖𝓕  = ((ℤ16.lst backCarry l) :𝓖𝓕).
Proof.
destruct l as [| h l]; intro Hlength.
- go.
- unfold backCarry.
  rewrite ZofList_cons.
  rewrite ZofList_cons.
  rewrite ZofList_app ; try omega.
  apply le_lt_eq_dec in Hlength.
  destruct Hlength.
  + rename l0 into H.
    replace (nth 15 (h :: l) 0) with 0.
    simpl in H.
    apply lt_S_n in H.
    replace (slice 14 l) with l.
    rewrite getResidute_0.
    rewrite getCarry_0.
    replace (ℤ16.lst [0]) with 0.
    f_equal.
    ring.
    go.
    symmetry.
    apply slice_length_le.
    omega.
    symmetry.
    apply nth_overflow.
    omega.
  + rename e into H.
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    destruct l ; [inversion H|].
    {
      clear H.
      replace (nth 15 [h; z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13] 0) with z13 by go.
      replace (slice 14 [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with 
      [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] by go.
      replace ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] ++ [ z13]) by go.
      rewrite ZofList_app ; try omega.
      replace (length [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12]) with 14%nat by go.
      replace (ℤ16.lst [getResidute 16 z13]) with (getResidute 16 z13) by go.
      replace (ℤ16.lst [z13]) with z13 by go.
      rewrite <- Zred_factor4.
      rewrite <- Zred_factor4.
      rewrite Zplus_assoc_reverse.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      symmetry.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      f_equal.
      f_equal.
      rewrite Z.add_shuffle3.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      symmetry.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      f_equal.
      f_equal.
      rewrite <- Z.add_mod_idemp_l by (compute ; omega).
      symmetry.
      rewrite Zmult_mod.
      rewrite <- t2256is38.
      rewrite <- Zmult_mod.
      rewrite Z.add_mod_idemp_l by (compute ; omega).
      replace 256 with (16 + 16 * 15) by omega.
      rewrite Z.pow_add_r by omega.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_mod.
      f_equal.
      f_equal.
      replace (2 ^ (16 * 15)) with (2 ^ (16 * 14) * 2 ^ 16) by (compute ; omega).
      replace (ℤ.ℕ 14) with 14 by (compute ; omega).
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod.
      f_equal.
      f_equal.
      rewrite Z.add_comm.
      rewrite residuteCarry ; go.
    }
    inversion H.
Qed.

Definition car25519 (l:list Z) : list Z := backCarry (Carrying_n 16 14 0 l).


Lemma car25519_ToFF_25519 : forall l, (length l = 16)%nat -> (ℤ16.lst l) :𝓖𝓕  = (ℤ16.lst car25519 l) :𝓖𝓕.
Proof.
intros l Hlength.
unfold car25519.
erewrite <- backCarry_ToFF_25519.
rewrite <- CarrynPreserve.
go.
go.
rewrite Carrying_n_length ; go.
Qed.

(* Yes I'm kinda cheating by fixing the length to 16 ! but it is still correct if
you were to compare to the tweetnacl implementation*)

