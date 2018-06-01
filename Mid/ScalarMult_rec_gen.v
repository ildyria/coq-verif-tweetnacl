Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Mid.ScalarMult_step_gen.
Require Import ssreflect.

Section ScalarRec.

Variable Zfa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zgetbit : Z -> Z -> Z.

Fixpoint Zabstract_rec (m : nat) (z a b c d e f x : Z) : (Z * Z * Z * Z * Z * Z) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := Zgetbit (Z.of_nat n) z in
      Zabstract_rec n z 
        (Zfa r a b c d e f x)
        (Zfb r a b c d e f x)
        (Zfc r a b c d e f x)
        (Zfd r a b c d e f x)
        (Zfe r a b c d e f x)
        (Zff r a b c d e f x)
        x
    end.

Definition Zstep_gen := Zstep_gen Zfa Zfb Zfc Zfd Zfe Zff Zgetbit.

Arguments rec_fn [T] _ _ _.

Definition abstract_rec_fn (z x:Z) (n:nat) (a b c d e f : Z) := rec_fn (Zstep_gen z x) n (a,b,c,d,e,f).

Lemma abstract_rec_equiv_rec_fn: forall n z a b c d e f x,
  Zabstract_rec n z a b c d e f x = abstract_rec_fn z x n a b c d e f.
Proof.
  induction n => z x a b c d e f.
  reflexivity.
  simpl.
  rewrite IHn /abstract_rec_fn.
  reflexivity.
Qed.

Close Scope Z.
End ScalarRec.