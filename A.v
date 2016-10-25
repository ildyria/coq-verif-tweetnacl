Require Export SumList.
Require Export ToFF.
Import ListNotations.

Open Scope Z.
Notation "A :𝓟" := (A mod (2^255 - 19)) (at level 80, right associativity).

Lemma ZsumListToFF : forall n a b o, a ⊕ b = o -> ToFF n a + ToFF n b = ToFF n o.
Proof.
intro n ; induction a , b.
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
  unfold ToFF.
  unfold ToFF.ToFF.
  rewrite <- Z.add_shuffle2.
  rewrite Zred_factor4.
  apply Zplus_eq_compat.
  apply Hh.
  f_equal.
  rewrite Z.add_comm.
  apply HSum.
Qed.

Corollary ZsumListToFF2: forall n a b, ToFF n (a ⊕ b) = ToFF n a + ToFF n b.
Proof.
intros n a b.
assert(exists o, o = a ⊕ b) by (exists (a ⊕ b) ; go) ; destruct H.
symmetry; subst x ; apply ZsumListToFF ; go.
Qed.

Lemma t2256is38 : (2^256 :𝓟 ) = (38 :𝓟).
Proof.
compute.
reflexivity.
(*
change 38 with (2 * 19).
change 256 with (Z.succ 255).
rewrite Z.pow_succ_r ; try omega.
rewrite <- Zmult_mod_idemp_r.
symmetry.
rewrite <- Zmult_mod_idemp_r.
f_equal.
*)
Qed.

Definition reduce n := 
  let c := n / 2^(256) in
  n + 38 * c - 2^(256) * c.

Lemma reduceFF : forall m, (reduce m :𝓟) = (m :𝓟).
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

Definition reduce_light_top n := 
  let c := n / 2^(16) in
  n - 2^(16) * c.

Definition reduce_light_bot n := 
  let c := n / 2^(16) in
  38 * c.

Definition backCarry (l:list Z) : (list Z) := 
  match l with
  | [] => []
  | h :: q => let v := nth 15 l 0 in
              (h + 38 * getCarry 16 v) :: slice 14 q ++ [getResidute 16 v]
  end.

Lemma getResidute_0 : forall n, getResidute n 0 = 0.
Proof.
go.
Qed.

Lemma getCarry_0 : forall n, getCarry n 0 = 0.
Proof.
intro n.
apply Z.shiftr_0_l.
Qed.

Lemma backCarry_ToFF : forall l, (length l <= 16)%nat -> ToFF 16 l :𝓟  = (ToFF 16 (backCarry l) :𝓟).
Proof.
destruct l as [| h l]; intro Hlength.
- go.
- unfold backCarry.
  rewrite ToFF_cons.
  rewrite ToFF_cons.
  rewrite ToFF_app ; try omega.
  apply le_lt_eq_dec in Hlength.
  destruct Hlength.
  + rename l0 into H.
    replace (nth 15 (h :: l) 0) with 0.
    simpl in H.
    apply lt_S_n in H.
    replace (slice 14 l) with l.
    rewrite getResidute_0.
    rewrite getCarry_0.
    replace (ToFF 16 [0]) with 0.
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
      rewrite ToFF_app ; try omega.
      replace (length [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12]) with 14%nat by go.
      replace (ToFF 16 [getResidute 16 z13]) with (getResidute 16 z13) by go.
      replace (ToFF 16 [z13]) with z13 by go.
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
