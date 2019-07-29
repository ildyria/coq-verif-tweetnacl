Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect eqtype ssrfun ssrbool ssrnat div.
From Tweetnacl.High Require Import ladder.
Require Import ZArith.
Require Import Tweetnacl.Mid.GetBit.

Lemma Zpow_Natpow n m : Z.pow (Z.of_nat n) (Z.of_nat m) = Z.of_nat (Nat.pow n m).
Proof.
elim: m n => // m IHm n.
rewrite [_ m.+1]Nat2Z.inj_succ Z.pow_succ_r; [|exact: Nat2Z.is_nonneg].
by rewrite IHm -Nat2Z.inj_mul -Nat.pow_succ_r; [|exact: Nat.le_0_l].
Qed.

Lemma Zof_nat_eqb n m : (Z.of_nat n =? Z.of_nat m)%Z = (n =? m).
Proof.
move Enm: (n =? m) => b.
case: b Enm.
+ by move/Nat.eqb_eq->; apply/Z.eqb_eq.
+ by move/Nat.eqb_neq=>H; apply/Z.eqb_neq; move/Nat2Z.inj.
Qed.

Lemma nat_eqb_ssr_eq n m : (n =? m) = (n == m).
Proof. by []. Qed.

Lemma Zodd_ssr_odd n : Z.odd (Z.of_nat n) = odd n.
Proof.
elim: n => // n IHn.
have ->: Z.odd (Z.of_nat n.+1) = ~~Z.odd (Z.of_nat n).
- by rewrite Nat2Z.inj_succ Z.odd_succ -Z.negb_odd.
by rewrite IHn.
Qed.

Lemma bitn0_1 n : (bitn n 0 == 1) = odd n.
Proof. by rewrite /bitn expn0 divn1 modn2 eqb1. Qed.

Lemma bitn0_0 n : (bitn n 0 == 0) = ~~odd n.
Proof. by rewrite /bitn expn0 divn1 modn2 eqb0. Qed.

Lemma two_induction (P : nat -> Prop) :
  P 0 -> P 1 -> (forall n, P n -> P n.+2) -> forall n, P n.
Proof.
move=> P0 P1 IHP.
suff: forall n, P (n.*2) /\ P(n.*2.+1) => [H n|];
  first by rewrite -[n]odd_double_half;
  case odd; [rewrite add1n|rewrite add0n]; elim: (H n./2).
elim=> // n IHn; rewrite doubleS.
by split; apply: IHP; elim: IHn.
Qed.

Lemma Nat_div_2_ssr_half n : n / 2 = n %/ 2.
Proof.
rewrite -Nat.div2_div divn2.
elim/two_induction: n => // n IHn.
by rewrite /= IHn.
Qed.

Lemma bitn_Ztestbit n k : Z.testbit (Z.of_nat n) (Z.of_nat k) = (bitn n k == 1).
Proof.
elim: k n => // [|k IHk] n; first by rewrite /= Zodd_ssr_odd bitn0_1.
rewrite Nat2Z.inj_succ -Z.div2_bits; last by exact: Zle_0_nat.
rewrite -/(Z.of_nat 2) -div_Zdiv; last by [].
rewrite IHk.
congr (_ == 1).
by rewrite Nat_div_2_ssr_half {1}/bitn -divnMA -expnS.
Qed.

Lemma Zland1_odd (x : Z) : (Z.land x 1 =? 1)%Z = Z.odd x.
Proof.
by rewrite -{1}[1%Z]/(Z.ones 1) Z.land_ones // Z.pow_1_r -Z.bit0_eqb Z.bit0_odd.
Qed.

Lemma Zland1_negodd (x : Z) : (Z.land x 1 =? 0)%Z = ~~ Z.odd x.
Proof.
rewrite -{1}[1%Z]/(Z.ones 1) Z.land_ones // Z.pow_1_r.
rewrite Zodd_mod.
assert({Zeq_bool (x mod 2) 1 = true} + {Zeq_bool (x mod 2) 1 = false}).
apply Sumbool.sumbool_of_bool.
assert( (0 <= x mod 2 < 2)%Z) by (apply Z_mod_lt ; omega).
assert((x mod 2 = 0 \/ x mod 2 = 1)%Z) by omega.
destruct H as [H|H]; rewrite H.
all: destruct H1 as [He|He].
1: rewrite He in H; compute in H ; discriminate.
1,2: rewrite He; reflexivity.
rewrite He in H; compute in H ; discriminate.
Qed.

Lemma Zgetbit_Ztestbit_1 (n k : Z) : (0 <= n)%Z -> (0 <= k)%Z -> (Mid.getbit k n =? 1)%Z = Z.testbit n k.
Proof. intros Hn Hk. rewrite /Mid.getbit.
destruct (k <? 0)%Z eqn:?.
apply Z.ltb_lt in Heqb.
omega.
destruct (n <? 0)%Z eqn:?.
apply Z.ltb_lt in Heqb0.
omega.
by rewrite Zland1_odd Z.testbit_odd.
Qed.

Lemma Zgetbit_Ztestbit_0 (n k : Z) : (0 <= n)%Z -> (0 <= k)%Z -> (Mid.getbit k n =? 0)%Z = ~~ Z.testbit n k.
Proof. intros Hn Hk. rewrite /Mid.getbit.
destruct (k <? 0)%Z eqn:?.
apply Z.ltb_lt in Heqb.
omega.
destruct (n <? 0)%Z eqn:?.
apply Z.ltb_lt in Heqb0.
omega.
by rewrite Zland1_negodd Z.testbit_odd.
Qed.

Lemma Zgetbit_bitn_1 (n k : nat) :
  (Mid.getbit (Z.of_nat k) (Z.of_nat n) =? 1)%Z = (bitn n k == 1).
Proof. rewrite Zgetbit_Ztestbit_1 ; [|apply Nat2Z.is_nonneg|apply Nat2Z.is_nonneg]. rewrite bitn_Ztestbit //. Qed.

Lemma Zgetbit_bitn_0 (n k : nat) :
  (Mid.getbit (Z.of_nat k) (Z.of_nat n) =? 0)%Z = (bitn n k == 0).
Proof.
rewrite Zgetbit_Ztestbit_0; [|apply Nat2Z.is_nonneg|apply Nat2Z.is_nonneg].
rewrite bitn_Ztestbit.
assert(H:= bitnV n k).
apply Bool.orb_prop in H;
destruct H as [H|H]; rewrite H;
apply Nat.eqb_eq in H; rewrite H ; reflexivity.
Qed.

Local Open Scope Z.
Local Lemma Zland1_b x:  0 <= (Z.land x 1) < 2.
Proof.
change 1 with (Z.ones 1).
rewrite Z.land_ones.
apply Z_mod_lt.
all: omega.
Qed.

Local Lemma Zland_0_1 x : (Z.land x 1) = 0 \/ (Z.land x 1) = 1.
Proof. assert(H:= Zland1_b x). omega. Qed.

Lemma shiftr0 x : Z.testbit (Z.land x 1) 0 = false <-> (Z.land x 1 = 0%Z).
Proof.
assert(Hl := Zland_0_1 x).
destruct Hl as [Hl|Hl] ; rewrite Hl ; simpl ; split ; intros ; trivial ; discriminate.
Qed.

Lemma shiftr1 x : Z.testbit (Z.land x 1) 0 = true <-> (Z.land x 1 = 1%Z).
Proof.
assert(Hl := Zland_0_1 x).
destruct Hl as [Hl|Hl] ; rewrite Hl ; simpl ; split ; intros ; trivial ; discriminate.
Qed.
Local Close Scope Z.

Lemma shiftr1b x : Z.testbit (Z.land x 1) 0 = (Z.to_nat (Z.land x 1) == 1).
Proof.
assert(Hl := Zland_0_1 x).
destruct Hl as [Hl|Hl] ; rewrite Hl ; simpl ; split ; intros ; trivial ; discriminate.
Qed.

Theorem Zgetbit_bitn : forall n k, Z.of_nat (bitn (Z.to_nat n) (Z.to_nat k)) = Mid.getbit k n.
Proof.
intros.
assert(Hn: (n < 0 \/ 0 <= n)%Z) by omega.
assert(Hk: (k < 0 \/ 0 <= k)%Z) by omega.
assert(H:= bitnV (Z.to_nat n) (Z.to_nat k)).
apply Bool.orb_prop in H.
destruct Hn as [Hn|Hn].
{
destruct H as [H|H];
assert(H2 := H);
apply Nat.eqb_eq in H; rewrite H;
simpl Z.of_nat; symmetry.
all: apply Z.eqb_eq.
1: rewrite -Zgetbit_bitn_0 in H2.
2: rewrite -Zgetbit_bitn_1 in H2.
all: rewrite /Mid.getbit.
all: destruct (n <? 0)%Z eqn:?.
reflexivity.
1,3: apply Z.ltb_ge in Heqb ; omega.
apply Z.ltb_lt in Heqb.
assert(HN0: Z.to_nat n = 0).
{
destruct n => //.
}
rewrite HN0 in H.
rewrite /bitn in H.
rewrite div0n in H ; compute in H ; omega.
}
{
destruct Hk as [Hk|Hk].
{
assert(HK0: Z.to_nat k = 0).
{
destruct k => //.
}
destruct H as [H|H];
assert(H2 := H);
apply Nat.eqb_eq in H; rewrite H;
simpl Z.of_nat; symmetry.
all: apply Z.eqb_eq.
1: rewrite -Zgetbit_bitn_0 in H2.
2: rewrite -Zgetbit_bitn_1 in H2.
rewrite HK0 in H2.
all: rewrite /Mid.getbit in H2.
all: rewrite /Mid.getbit.
all: replace (Z.of_nat 0 <? 0)%Z with false in H2.
2,4: reflexivity.
all: destruct (k <? 0)%Z eqn:?.
all: try solve[apply Z.ltb_ge in Heqb ; omega].
all: rewrite (Z2Nat.id n) in H2 => //.
rewrite HK0 in H2; simpl in H2 ; assumption.
}
destruct H as [H|H];
assert(H2 := H);
apply Nat.eqb_eq in H; rewrite H.
1: rewrite -Zgetbit_bitn_0 in H2.
2: rewrite -Zgetbit_bitn_1 in H2.
all: rewrite ?Z2Nat.id in H2 => //.
all: simpl.
all: apply Z.eqb_eq in H2 => //.
}

Qed.