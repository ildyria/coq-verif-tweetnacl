Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype ssralg.
From Tweetnacl.High Require Import mc Zmodp.

Open Scope ring_scope.
Import GRing.Theory.

Definition a : Zmodp.type := Zmodp.pi 486662.
Definition b : Zmodp.type := 1%R.

Lemma asq_neq4 : a^+2 != 4%:R.
Proof. by rewrite eqE expr2 /a Zmodp_mulE /=; unlock p. Qed.

Lemma b_neq0 : b != 0.
Proof. exact: oner_neq0. Qed.

Definition curve25519Type := Build_mcuType b_neq0 asq_neq4.
