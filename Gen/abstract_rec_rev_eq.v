From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.

Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Libs Require Import HeadTailRec.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import step_gen.

From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import abstract_rec.
From Tweetnacl.Gen Require Import abstract_rec_rev.

Require Import ssreflect.

Section EquivFnRec.

Open Scope Z.

Context {T : Type}.
Context {O : Ops T}.

Lemma abstract_fn_rev_eq : forall m p z a b c d e f x,
  0 <= m ->
  0 <= p ->
  m <= p + 1 ->
  abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x = 
  abstract_fn_rev m p z a b c d e f x.
Proof.
  intros m p z a b c d e f x Hm.
  gen p z a b c d e f x.
  pattern m.
  eapply natlike_ind.
  - intros; rewrite abstract_fn_rev_equation Zle_imp_le_bool ; try omega ; reflexivity.
  - clear Hm m; intros m Hm IHm p z a b c d e f x Hp Hmpp.
    sort. (* sort the hypothesises *)
  assert(Hmp: m <= p + 1) by omega.
  change (Z.succ m) with (m + 1).
  replace (Z.to_nat (m + 1)) with (S (Z.to_nat m)).
  2:   rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite abstract_fn_rev_equation /abstract_fn_rev_n.
  2: omega. simpl.
  remember (abstract_rec_rev (Z.to_nat m) (Z.to_nat p) z a b c d e f x) as k ; destruct k as (((((a0,b0),c0),d0),e0),f0).
  replace (m + 1 - 1) with m by omega.
  remember (abstract_fn_rev m p z a b c d e f x) as k' ; destruct k' as (((((a0',b0'),c0'),d0'),e0'),f0').
  assert((a0, b0, c0, d0, e0, f0) = (a0', b0', c0', d0', e0', f0')).
  rewrite Heqk' Heqk.
  apply IHm ; omega.
  inversion H ; subst.
  replace (m + 1 <=? 0) with false.
  do 7 f_equal ; rewrite -Z2Nat.inj_sub ; try omega ; apply Z2Nat.id; omega.
  symmetry.
  apply Z.leb_gt.
  omega.
Qed.

Close Scope Z.

Lemma abstract_rec_rev_eq : forall n z a b c d e f x,
  abstract_rec (S n) z a b c d e f x = abstract_rec_rev (S n) n z a b c d e f x.
Proof.
intros.
rewrite abstract_rec_equiv_rec_fn abstract_rec_rev_equiv_rec_fn_S_n.
rewrite /abstract_rec_fn_rev /abstract_rec_fn /abstract_rec_fn Tail_Head_equiv ;f_equal.
Qed.

End EquivFnRec.