Require Import stdpp.list.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Low.Carry_n.

Local Open Scope Z.

Definition backCarry (l:list Z) : (list Z) := 
  match l with
  | [] => []
  | h :: q => let v := nth 15 l 0 in
              (h + 38 * getCarry 16 v) :: take 14 q ++ [getResidue 16 v]
  end.

Lemma backCarry_ToFF_25519 : forall l, Zlength l <= 16 -> (ℤ16.lst l) :𝓖𝓕  = ((ℤ16.lst backCarry l) :𝓖𝓕).
Proof.
  destruct l as [| h l]; intro Hlength.
  - go.
  - unfold backCarry.
    repeat rewrite ZofList_cons.
    rewrite ZofList_app ; try omega.
    rewrite Zlength_cons' in Hlength.
    apply Z_le_lt_eq_dec in Hlength.
    destruct Hlength.
    + rename l0 into H.
      assert(Zlength l < 15) by omega.
      rewrite Zlength_correct in H0.
      repeat match goal with 
       | _ => simpl; omega
       | _ => rewrite nth_overflow
       | _ => rewrite take_ge
       | _ => rewrite getResidue_0
       | _ => rewrite getCarry_0
       | _ => rewrite ZofList_cons_0
       | _ => f_equal ; ring
       end.
    + rename e into H.
      assert((length l = 15)%nat) by (rewrite Zlength_correct in H ; omega).
      repeat (destruct l ; tryfalse).
      clear H H0.
      unfold nth , take.
      change ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13]) with ([z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12] ++ [ z13]).
      rewrite ZofList_app ; try omega.
      repeat rewrite ZofList_cons_0.
      do 2 rewrite <- Zred_factor4 ; rewrite Zplus_assoc_reverse.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega);symmetry;rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      f_equal; f_equal.
      rewrite Z.add_shuffle3.
      rewrite <- Z.add_mod_idemp_r by (compute ; omega);symmetry;rewrite <- Z.add_mod_idemp_r by (compute ; omega).
      f_equal; f_equal.
      rewrite <- Z.add_mod_idemp_l by (compute ; omega) ; symmetry.
      rewrite Zmult_mod.
      rewrite <- t2256is38.
      rewrite <- Zmult_mod.
      rewrite Z.add_mod_idemp_l.
      change 256 with (16 + 16 * 15).
      orewrite Z.pow_add_r.
      rewrite Zmult_assoc_reverse.
      rewrite Zred_factor4.
      rewrite Zmult_mod ; symmetry ; rewrite Zmult_mod.
      f_equal;f_equal.
      change (2 ^ (16 * 15)) with (2 ^ (16 * 14) * 2 ^ 16).
      rewrite Zmult_mod.
      symmetry.
      rewrite Zmult_assoc_reverse ; rewrite Zred_factor4 ; rewrite Zmult_mod.
      f_equal; f_equal.
      rewrite Z.add_comm.
      rewrite residuteCarry ; go.
      compute; omega.
Qed.

Close Scope Z.