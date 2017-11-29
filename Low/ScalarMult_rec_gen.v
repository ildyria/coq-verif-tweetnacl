Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Require Import Tweetnacl.Low.ScalarMult_step_gen.

Section ScalarRec.

Variable fa : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fb : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fc : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fd : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fe : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable ff : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Fixpoint abstract_rec (m : nat) (z a b c d e f x : list Z) : (list Z * list Z * list Z * list Z * list Z * list Z) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat n) z in
      abstract_rec n z 
        (fa r a b c d e f x)
        (fb r a b c d e f x)
        (fc r a b c d e f x)
        (fd r a b c d e f x)
        (fe r a b c d e f x)
        (ff r a b c d e f x)
        x
    end.

Definition step_gen := step_gen fa fb fc fd fe ff getbit.

Arguments rec_fn [T] _ _ _.

Definition abstract_rec_fn (z x:list Z) (n:nat) (a b c d e f : list Z) := rec_fn (step_gen z x) n (a,b,c,d,e,f).

Lemma abstract_rec_equiv_rec_fn: forall n z a b c d e f x,
  abstract_rec n z a b c d e f x = abstract_rec_fn z x n a b c d e f.
Proof.
  induction n => z x a b c d e f.
  reflexivity.
  simpl.
  rewrite IHn /abstract_rec_fn.
  reflexivity.
Qed.

Close Scope Z.
End ScalarRec.