From Tweetnacl Require Export Libs.LibTactics.
From Tweetnacl Require Export Libs.LibTactics_SF.
Require Import Coq.micromega.Lia.
Require Import ssreflect.
Require Import Recdef.

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

Section fun_bool_rec.

(* Context (n_min:Z). (* (Hn : 0 <= n). *) *)

Definition dec_proof_fun (n_min a  : Z) : nat := Z.to_nat (a - n_min).

Function forall_Z (n_min:Z) (a:Z) (P:Z -> bool) {measure (dec_proof_fun n_min) a} : bool :=
  if (a <=? n_min)
    then true
    else
      andb (P (a - 1)) (forall_Z n_min (a - 1) P).
Proof. intros. apply Z2Nat.inj_lt; apply Z.leb_gt in teq; omega. Defined.

(* Lemma forall_Z_translate: forall n_min n_max P,
  n_min <= n_max ->
  forall_Z n_min n_max P = forall_Z 0 (n_max - n_min) (fun x => P (x + n_min)).
Proof.
intros.
assert(exists n, (n_max - n_min) = Z.of_nat n).
apply Z_of_nat_complete; omega.
destruct H0 as [n Hn].
revert Hn.
revert H.
revert n_min n_max.
induction n ; intros.
revert Hn. change_Z_of_nat => Hn.
assert(n_max = n_min) by omega.
subst.
rewrite Hn.
rewrite forall_Z_equation. symmetry. rewrite forall_Z_equation.
rewrite ?Zle_imp_le_bool.
omega.
omega.
reflexivity.
rewrite Nat2Z.inj_succ in Hn.
change (Z.succ ?A) with (A + 1) in Hn.
assert(n_max = n_min + Z.of_nat n + 1).
omega.
rewrite forall_Z_equation. symmetry. rewrite forall_Z_equation.
replace (n_max - n_min <=? 0) with false.
2: symmetry ; apply Z.leb_gt ; omega.
replace (n_max <=? n_min) with false.
2: symmetry ; apply Z.leb_gt ; omega.
fequals.
fequals.
omega.
symmetry.
assert(n_max - n_min - 1 = Z.of_nat n).
omega.
replace (n_max - n_min - 1) with (n_max - 1 - n_min).
2: omega.
apply IHn ; omega.
Qed.
 *)
Lemma forall_Z_refl : forall (P: Z -> bool) (n_min n_max: Z),
  (forall i, n_min <= i < n_max -> P i = true) <-> forall_Z n_min n_max P = true.
Proof.
intros P n_min n_max.
assert(n_max <= n_min \/ n_min <= n_max).
omega.
destruct H as [Hminmax|Hminmax] ; split ; intros; try omega.
rewrite forall_Z_equation.
rewrite Zle_imp_le_bool.
omega.
reflexivity.
(* -> *)
assert(Hn: exists n, (n_max - n_min) = Z.of_nat n).
apply Z_of_nat_complete; omega.
destruct Hn as [n Hn].
revert H.
revert Hn.
revert Hminmax.
revert n_min n_max.
induction n ; intros.
revert Hn. change_Z_of_nat => Hn.
assert(n_max = n_min) by omega.
rewrite forall_Z_equation.
rewrite ?Zle_imp_le_bool.
omega.
reflexivity.
rewrite Nat2Z.inj_succ in Hn.
change (Z.succ ?A) with (A + 1) in Hn.
assert(n_max = n_min + Z.of_nat n + 1).
omega.
rewrite forall_Z_equation.
replace (n_max <=? n_min) with false.
2: symmetry ; apply Z.leb_gt ; omega.
apply andb_true_iff ; split.
apply H.
omega.
apply IHn.
omega.
omega.
intros ; apply H ; omega.
(* <- *)
assert(Hn: exists n, (n_max - n_min) = Z.of_nat n).
apply Z_of_nat_complete; omega.
destruct Hn as [n Hn].
revert H.
revert H0.
revert Hn.
revert Hminmax.
revert n_min n_max i.
induction n ; intros.
revert Hn. change_Z_of_nat => Hn.
omega.
rewrite Nat2Z.inj_succ in Hn.
change (Z.succ ?A) with (A + 1) in Hn.
assert(n_max = n_min + Z.of_nat n + 1).
omega.
rewrite forall_Z_equation in H.
replace (n_max <=? n_min) with false in H.
2: symmetry ; apply Z.leb_gt ; omega.
apply andb_true_iff in H ; destruct H as [Hi Hi1].
assert(i < n_max - 1 \/ i = n_max - 1).
omega.
destruct H.
2: rewrite H ; assumption.
eapply IHn.
4: apply Hi1.
omega.
omega.
omega.
Qed.

Function forall_Z_Z (m_min:Z) (m_max:Z) (n_min:Z) (a:Z) (P:Z -> Z -> bool)
  {measure (dec_proof_fun n_min) a} : bool :=
  if (a <=? n_min)
    then true
    else
      andb (forall_Z m_min m_max (P (a - 1))) (forall_Z_Z m_min m_max n_min (a - 1) P).
Proof. intros; apply Z2Nat.inj_lt; apply Z.leb_gt in teq; omega. Defined.

Lemma forall_Z_Z_refl : forall (P: Z -> Z -> bool) (m_min m_max: Z) (n_min n_max: Z),
  (forall i j, n_min <= i < n_max -> m_min <= j < m_max -> P i j = true) <-> forall_Z_Z m_min m_max n_min n_max P = true.
Proof.
intros P m_min m_max n_min n_max.
assert(n_max <= n_min \/ n_min <= n_max).
omega.
destruct H as [Hminmax|Hminmax] ; split ; intros; try omega.
rewrite forall_Z_Z_equation.
rewrite Zle_imp_le_bool.
omega.
reflexivity.
(* -> *)
assert(Hn: exists n, (n_max - n_min) = Z.of_nat n).
apply Z_of_nat_complete; omega.
destruct Hn as [n Hn].
revert H.
revert Hn.
revert Hminmax.
revert m_min m_max.
revert n_min n_max.
induction n ; intros.
revert Hn. change_Z_of_nat => Hn.
assert(n_max = n_min) by omega.
rewrite forall_Z_Z_equation.
rewrite ?Zle_imp_le_bool.
omega.
reflexivity.

rewrite Nat2Z.inj_succ in Hn.
change (Z.succ ?A) with (A + 1) in Hn.
assert(n_max = n_min + Z.of_nat n + 1).
omega.
rewrite forall_Z_Z_equation.
replace (n_max <=? n_min) with false.
2: symmetry ; apply Z.leb_gt ; omega.
apply andb_true_iff ; split.
apply forall_Z_refl ; intros.
apply H ; omega.
apply IHn ; try omega.
intros ; apply H ; omega.

(* <- *)
assert(Hn: exists n, (n_max - n_min) = Z.of_nat n).
apply Z_of_nat_complete; omega.
destruct Hn as [n Hn].
revert H.
revert H0.
revert H1.
revert Hn.
revert Hminmax.
revert m_min m_max.
revert n_min n_max i.
induction n ; intros.
revert Hn. change_Z_of_nat => Hn.
omega.
rewrite Nat2Z.inj_succ in Hn.
change (Z.succ ?A) with (A + 1) in Hn.
assert(n_max = n_min + Z.of_nat n + 1).
omega.
rewrite forall_Z_Z_equation in H.
replace (n_max <=? n_min) with false in H.
2: symmetry ; apply Z.leb_gt ; omega.
apply andb_true_iff in H ; destruct H as [Hi Hi1].
assert(i < n_max - 1 \/ i = n_max - 1).
omega.
destruct H.
eapply IHn.
5: apply Hi1.
all : try omega.
subst i.
assert(Hnn:=forall_Z_refl (P (n_max - 1)) m_min m_max).
apply Hnn.
assumption.
omega.
Qed.

End fun_bool_rec.


(* Ltac gen_goals H P j n := match n with 
  | 0 => idtac
  | n => 
    let n'' := (eval compute in (j - n)) in
    assert(P n'');
     [change (n'') with ((n'' - 1) + 1) ;
     simpl Z.sub ; apply H ; go|];
   let n' := (eval compute in (n - 1)) in
   gen_goals H P j n'
  end.
 *)
Lemma P016_impl : forall (P : Z -> Prop) , P 1 -> 
  (forall i, 0 < i < 16 -> P i -> P (i + 1)) -> 
  forall i, 0 < i < 16 -> P i.
Proof.
intros P P1 Hind i.
pattern i.
destruct i.
try omega.
2: assert(Hp:= Zlt_neg_0 p) ; try omega.
induction p using Pos.peano_ind.
intros ; assumption.
replace ((Z.pos (Pos.succ p))) with (Z.pos p + 1) by lia.
intros Hp1.
apply Hind.
lia.
apply IHp ; lia.
Qed.

Close Scope Z.