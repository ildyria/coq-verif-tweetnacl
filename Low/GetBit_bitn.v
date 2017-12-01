Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect eqtype ssrfun ssrbool ssrnat div.
From Tweetnacl.High Require Import ladder.
Require Import ZArith.

(* Lemma Zpow_Natpow n m : Z.pow (Z.of_nat n) (Z.of_nat m) = Z.of_nat (Nat.pow n m).
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
Proof. by []. Qed. *)

Lemma Zodd_ssr_odd n : Z.odd (Z.of_nat n) = odd n.
Proof.
elim: n => // n IHn.
have ->: Z.odd (Z.of_nat n.+1) = ~~Z.odd (Z.of_nat n).
- by rewrite Nat2Z.inj_succ Z.odd_succ -Z.negb_odd.
by rewrite IHn.
Qed.

Lemma bitn0_1 n : (bitn n 0 == 1) = odd n.
Proof. by rewrite /bitn expn0 divn1 modn2 eqb1. Qed.

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

Lemma getbit_bitn x i : Z.to_nat (Z.land (Z.shiftr x i) 1) = bitn (Z.to_nat x) (Z.to_nat i).
Proof.
Admitted.