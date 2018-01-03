From Tweetnacl Require Export Libs.LibTactics.
Require Import ssreflect.

Lemma orFalse : forall (P:Prop), P \/ False <-> P.
Proof. boum. Qed.

Lemma Falseor : forall (P:Prop), False \/ P <-> P.
Proof. boum. Qed.

Lemma andTrue : forall (P:Prop), P /\ True <-> P.
Proof. boum. Qed.

Lemma Trueand : forall (P:Prop), True /\ P <-> P.
Proof. boum. Qed.

Fixpoint forall_nat (i:nat) (P:nat -> bool) := match i with 
  | 0 => true
  | S n => andb (P n) (forall_nat n P)
  end.

Lemma forall_nat_refl : forall (P: nat -> bool) (n: nat),
  (forall i, 0 <= i < n -> P i = true) <-> forall_nat n P = true.
Proof. intros P; split ; induction n as [|n IHn]; move => H  ; go.
simpl ; apply andb_true_iff ; go.
intros.
simpl in H ; apply andb_true_iff in H ; destruct H as [Hn HPi].
assert(Hi: 0 <= i < n \/ i = n) by omega.
clear H0 ; destruct Hi as [Hi|Hi] ; go.
Qed.

Fixpoint forall_nat_nat (i:nat) (j:nat) (P:nat -> nat -> bool) := match i with
  | 0 => true
  | S n => andb (forall_nat j (P n)) (forall_nat_nat n j P)
  end.

Lemma forall_nat_nat_refl : forall (P:nat -> nat-> bool) (n n':nat),
  (forall i j, 0 <= i < n -> 0 <= j < n' -> P i j = true) <-> forall_nat_nat n n' P = true.
Proof.
intros P; split ; induction n as [|n IHn]; move => H  ; go.
simpl ; rewrite ?andb_true_iff ; split ; try split;  go.
apply forall_nat_refl ; intros ; apply H; omega.
intros i j His Hjs.
simpl in H ; apply andb_true_iff in H ; destruct H as [Hn HPi].
assert(Hi: 0 <= i < n \/ i = n) by omega.
clear His ; destruct Hi as [Hi|Hi] ; go.
subst.
assert(Hnn:=forall_nat_refl (P n) n').
destruct Hnn as [Hinv Hdirect].
go.
Qed.

Open Scope Z.

Ltac gen_goals H P j n := match n with 
  | 0 => idtac
  | n => 
    let n'' := (eval compute in (j - n)) in
    assert(P n'');
     [change (n'') with ((n'' - 1) + 1) ;
     simpl Z.sub ; apply H ; go|];
   let n' := (eval compute in (n - 1)) in
   gen_goals H P j n'
  end.

Lemma P016_impl : forall (P : Z -> Prop) , P 1 -> 
  (forall i, 0 < i < 16 -> P i -> P (i + 1)) -> 
  forall i, 0 < i < 16 -> P i.
Proof.
intros P HP1 HPInd i Hi.
gen_goals HPInd P 16 14.
assert_gen_hyp i 15 14. omega.
repeat match goal with
  | _ => subst i ; assumption
  | [ H : _ \/ _ |- _ ] => destruct H
end.
Qed.

Close Scope Z.