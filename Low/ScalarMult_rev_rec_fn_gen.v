Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_rec_gen.
Require Import Tweetnacl.Low.ScalarMult_rev_rec_gen.
Require Import Tweetnacl.Low.ScalarMult_rev_fn_gen.
Require Import Tweetnacl.Libs.HeadTailRec.

Section EquivFnRec.

Variable fa : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fb : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fc : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fd : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fe : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable ff : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Definition abstract_rec := abstract_rec fa fb fc fd fe ff getbit.
Definition abstract_rec_rev := abstract_rec_rev fa fb fc fd fe ff getbit.
Definition abstract_fn_rev := abstract_fn_rev fa fb fc fd fe ff getbit.

Open Scope Z.

Lemma abstract_fn_rev_eq : forall m p z a b c d e f x,
  0 <= m ->
  0 <= p ->
  m <= p + 1 ->
  abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = 
  abstract_fn_rev m p z a b c d e f x.
Proof.
  intros m p z a b c d e f x Hm.
  gen p z a b c d e f x.
  gen m.
  apply (natlike_ind (fun m => forall (p : ℤ) (z a b c d e f x : list ℤ),
0 <= p -> m <= p + 1  -> abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = abstract_fn_rev m p z a b c d e f x)).
  - intros; rewrite /abstract_fn_rev abstract_fn_rev_equation Zle_imp_le_bool ; try omega ; reflexivity.
  - intros m Hm IHm p z a b c d e f x Hp Hmpp.
    sort. (* sort the hypothesises *)
  assert(Hmp: m <= p + 1) by omega.
  change (Z.succ m) with (m + 1).
  replace (Z.to_nat (m + 1)) with (S (Z.to_nat m)).
  2:   rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite /abstract_fn_rev abstract_fn_rev_n.
  2: omega. simpl.
  fold abstract_fn_rev.
  remember (abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  replace (m + 1 - 1) with m by omega.
  remember (abstract_fn_rev m p z a b c d e f x) as k' ; destruct k' as (((((a0',b0'),c0'),d0'),e0'),f0').
  assert((a0, b0, c0, d0, e0, f0) = (a0', b0', c0', d0', e0', f0')).
  rewrite Heqk' Heqk.
  apply IHm ; omega.
  inversion H ; subst.
  do 7 f_equal ; rewrite -Z2Nat.inj_sub ; try omega ; apply Z2Nat.id; omega.
Qed.

Close Scope Z.

Lemma abstract_rec_rev_eq : forall n z a b c d e f x,
  abstract_rec (S n) z a b c d e f x = abstract_rec_rev (S n) n z a b c d e f x.
Proof.
intros.
rewrite /abstract_rec /abstract_rec_rev.
rewrite abstract_rec_equiv_rec_fn.
rewrite abstract_rec_rev_equiv_rec_fn.
rewrite /abstract_rec_fn /ScalarMult_rec_gen.abstract_rec_fn.
rewrite Tail_Head_equiv.
f_equal.
Qed.

End EquivFnRec.
