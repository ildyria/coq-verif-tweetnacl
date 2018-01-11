From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
(* From Tweetnacl Require Import Mid.SubList. *)
(* From Tweetnacl Require Import Low.Get_abcdef. *)
(* From Tweetnacl Require Import Low.GetBit_pack25519. *)
(* From Tweetnacl Require Import Low.Sel25519. *)
(* From Tweetnacl Require Import Low.Constant. *)
(* From Tweetnacl Require Import Libs.Lists_extended.
From Tweetnacl Require Import Libs.List_Ltac.
From Tweetnacl Require Import Libs.LibTactics_SF.
From Tweetnacl Require Import Libs.LibTactics.
 *)
From stdpp Require Import prelude.
Require Import Recdef.

(*
sv pack25519(u8 *o,const gf n)
{
  int i,j,b;
  gf m,t;
  FOR(i,16) t[i]=n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  FOR(j,2) {
    m[0]=t[0]-0xffed;

    for(i=1;i<15;i++) {
      m[i]=t[i]-0xffff-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }

    for(i=1;i<15;i++) {
      m[i]=t[i];
    }
    for(i=1;i<15;i++) {
      m[i]=m[i]-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }




    m[15]=t[15]-0x7fff-((m[14]>>16)&1);
    b=(m[15]>>16)&1;
    m[14]&=0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]&0xff;
    o[2*i+1]=t[i]>>8;
  }
}
*)

Open Scope Z.
(*
0xffff = 65535
0xffed = 65517
0x7fff = 32767
*)

(* Definition subst_0xffed t := t - 65517. *)
Definition subst_0xffffc t m := t - 65535 - (Z.land (Z.shiftr m 16) 1).
(* Definition subst_0xffff t := t - 65535. *)
(* Definition subst_0x7fffc t m := t - 32767 - (Z.land (Z.shiftr m 16) 1). *)
(* Definition subst_0x7fff t := t - 32767. *)
(* Definition subst_c t m := t - (Z.land (Z.shiftr m 16) 1). *)
Definition mod0xffff m := Z.land m 65535.

Definition sub_step (a:Z) (m t:list Z) : list Z :=
    let m' := nth (Z.to_nat (a - 1)) m 0 in
    let t' := nth (Z.to_nat a) t 0 in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (subst_0xffffc t' m')) (mod0xffff m').

Lemma nth_i_1_substep: forall i m t, 
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  nth (Z.to_nat (i - 1)) (sub_step i m t) 0 = mod0xffff (nth (Z.to_nat (i - 1)) m 0).
Proof.
  intros i m t Hmt Him.
  unfold sub_step, mod0xffff.
  rewrite upd_nth_same_Zlength ; try reflexivity.
  split ; try omega ; rewrite upd_nth_Zlength ; rewrite Z2Nat.id ; try omega.
Qed.

Lemma nth_i_substep: forall i m t, 
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  nth (Z.to_nat (i)) (sub_step i m t) 0 = subst_0xffffc (nth (Z.to_nat i) t 0) (nth (Z.to_nat (i - 1)) m 0).
Proof.
  intros i m t Hmt Him.
  unfold sub_step.
  rewrite upd_nth_diff_Zlength.
  2: split ; try omega ; rewrite upd_nth_Zlength ; rewrite Z2Nat.id ; try omega.
  2: split ; try omega ; rewrite upd_nth_Zlength ; rewrite Z2Nat.id ; try omega.
  2: intros H ; apply (f_equal Z.of_nat) in H ; rewrite ?Z2Nat.id in H ; omega.
  rewrite upd_nth_same_Zlength ; try reflexivity.
  rewrite Z2Nat.id ; try omega.
Qed.

(* Definition of the for loop : 1 -> 15 *)
Function sub_fn_rev {A} (f:Z -> list A -> list A -> list A) (a:Z) (m t: list A) {measure Z.to_nat a} : (list A) :=
  if (a <=? 1)
    then m
    else
      let prev := sub_fn_rev f (a - 1) m t in 
        f (a - 1) prev t.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Arguments sub_fn_rev [_] _ _ _.

Lemma sub_fn_rev_1 : forall A f (m t:list A),
  sub_fn_rev f 1 m t = m.
Proof. intros. reflexivity. Qed.

Lemma sub_fn_rev_n : forall A f (m t:list A) a,
  1 < a ->
  sub_fn_rev f a m t = f (a - 1) (sub_fn_rev f (a - 1) m t) t.
Proof. intros. rewrite sub_fn_rev_equation.
destruct (a <=? 1) eqn:Eq.
apply Zle_bool_imp_le in Eq; omega.
reflexivity.
Qed.

(* Definition of the for loop : 1 -> 15 *)
Function sub_fn_rev_s {A} (f:Z -> list A -> list A) (a:Z) (m: list A) {measure Z.to_nat a} : (list A) :=
  if (a <=? 1)
    then m
    else
      let prev := sub_fn_rev_s f (a - 1) m in 
        f (a - 1) prev.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Arguments sub_fn_rev_s [_] _ _ _.

Lemma sub_fn_rev_s_1 : forall A f (m: list A),
  sub_fn_rev_s f 1 m = m.
Proof. intros. reflexivity. Qed.

Lemma sub_fn_rev_s_n : forall A a (m: list A) f,
  1 < a ->
  sub_fn_rev_s f a m = f (a - 1) (sub_fn_rev_s f (a - 1) m).
Proof. intros. rewrite sub_fn_rev_s_equation.
destruct (a <=? 1) eqn:Eq.
apply Zle_bool_imp_le in Eq; omega.
reflexivity.
Qed.

Lemma nth_i_1_substep_bounds: forall i m t,
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  0 <= nth (Z.to_nat (i - 1)) (sub_step i m t) 0 < 2^16.
Proof.
  intros.
  rewrite nth_i_1_substep ; auto.
  unfold mod0xffff.
  change 65535 with (Z.ones 16).
  rewrite Z.land_ones ; try omega.
  apply Z_mod_lt.
  apply pown0 ; omega.
Qed.

Lemma nth_i_substep_bounds: forall i m t,
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  Forall (fun x => 0 <= x < 2^16) t ->
  -2^16 <= nth (Z.to_nat i) (sub_step i m t) 0 <= 0.
Proof.
intros i m t Hmt Him HPt.
rewrite nth_i_substep ; auto.
unfold subst_0xffffc.
assert(HP0: 0 ≤ 0 ∧ 0 < 2 ^ 16) by (split ; try omega ; apply Z.gt_lt ; apply pown0 ; omega).
assert(0 ≤ (nth (Z.to_nat i) t 0) ∧ (nth (Z.to_nat i) t 0) < 2 ^ 16).
apply Forall_nth_d; assumption.
assert(HZlandminmax:= and_0_or_1 (nth (Z.to_nat (i - 1)) m 0 ≫ 16)).
assert(HZland: Z.land (nth (Z.to_nat (i - 1)) m 0 ≫ 16) 1 = 0 \/ Z.land (nth (Z.to_nat (i - 1)) m 0 ≫ 16) 1 = 1) by omega.
destruct HZland as [HZland|HZland]; rewrite HZland.
all: change (2^16) with 65536 in * ; omega.
Qed.

Lemma subst_select_step_Zlength : forall i m t,
  0 < i < Zlength m->
  Zlength (sub_step i m t) = Zlength m.
Proof.
  intros.
  unfold sub_step.
  assert(0 < Z.to_nat i /\ Z.to_nat i < Zlength m) by (rewrite ?Z2Nat.id ; omega).
  assert(Z.of_nat (Z.to_nat (i - 1)) = (Z.of_nat (Z.to_nat i)) - 1) by (rewrite ?Z2Nat.id ; omega).
  repeat rewrite ?upd_nth_Zlength ; try omega.
Qed.

Local Lemma sub_fn_rev_Zlength_ind_step : forall i m t,
  0 < i < Zlength m ->
  Zlength (sub_fn_rev sub_step i m t) = Zlength m ->
  Zlength (sub_fn_rev sub_step (i+1) m t) = Zlength m.
Proof.
intros i m t Him Hind.
rewrite sub_fn_rev_equation.
flatten.
replace ( i + 1 - 1) with i by omega.
rewrite <- Hind.
apply subst_select_step_Zlength.
rewrite Hind.
assumption.
Qed.

Lemma sub_fn_rev_Zlength : forall i m t,
  Zlength m = 16 ->
  0 < i < Zlength m ->
  Zlength (sub_fn_rev sub_step i m t) = Zlength m.
Proof.
intros.
change(Zlength (sub_fn_rev sub_step i m t) = Zlength m) with
  ((fun x => Zlength (sub_fn_rev sub_step x m t) = Zlength m) i).
apply P016_impl.
by rewrite sub_fn_rev_1.
intros ; apply sub_fn_rev_Zlength_ind_step.
2: apply H2.
all: omega.
Qed.


Close Scope Z.