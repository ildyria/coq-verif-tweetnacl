Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import montgomery_rec.
From Tweetnacl.Gen Require Import montgomery_rec_swap.

Open Scope Z.

Section Montgomery_Rec_Swap_Eq.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Hypothesis Getbit_01 : forall n z, Getbit n z = 0 \/ Getbit n z = 1.
Hypothesis Sel25519_1 : forall p q, Sel25519 1 p q = q.
Hypothesis Sel25519_0 : forall p q, Sel25519 0 p q = p.

Local Lemma Zlxor_1_1 : Z.lxor 1 1 = 0.
Proof. trivial. Qed.

Opaque Z.lxor.

Ltac rewritesXorSel := rewrite ?Z.lxor_0_l ?Z.lxor_0_r ?Zlxor_1_1 ?Sel25519_1 ?Sel25519_0.

Lemma montgomery_rec_swap_01 : forall (n:nat) z a b c d e f x,
  montgomery_rec_swap n z a b c d e f x 0 =
  montgomery_rec_swap n z b a d c e f x 1.
Proof.
  induction n as [|n IHn] => z a b c d e f x /=.
  2: assert(Hgetbit := Getbit_01 (ℤ.ℕ n) z).
  2: move: Hgetbit => [] ->.
  all: rewritesXorSel ; reflexivity.
Qed.

Theorem montgomery_rec_swap_eq: forall n z a b c d e f x,
  montgomery_rec_swap n z a b c d e f x 0 =
  montgomery_rec n z a b c d e f x.
Proof.
  induction n as [|n IHn] ; move=> z a b c d e f x /=.
  - rewritesXorSel => //.
  - assert(Hgetbit := Getbit_01 (ℤ.ℕ n) z).
    move: Hgetbit => [] ->.
    rewritesXorSel.
    apply IHn.
    rewritesXorSel.
    rewrite -montgomery_rec_swap_01.
    apply IHn.
Qed.

End Montgomery_Rec_Swap_Eq.