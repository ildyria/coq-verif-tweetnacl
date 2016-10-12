Require Export SumList.
Require Export ToFF.
Import ListNotations.

Open Scope Z.

Lemma ZsumListToFF : forall n a b o, ZsumList a b = o -> ToFF n a + ToFF n b = ToFF n o.
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

Corollary ZsumListToFF2: forall n a b, ToFF n (ZsumList a b) = ToFF n a + ToFF n b.
Proof.
intros n a b.
assert(exists o, o = ZsumList a b) by (exists (ZsumList a b) ; go) ; destruct H.
symmetry; subst x ; apply ZsumListToFF ; go.
Qed.


Lemma t2256is38 : Z.pow 2 256 mod (Z.pow 2 255 - 19) = 38 mod (Z.pow 2 255 - 19).
Proof.
compute.
go.
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

Lemma reduceFF : forall m, (reduce m) mod (2^255 - 19) = m mod (2^255 - 19).
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

