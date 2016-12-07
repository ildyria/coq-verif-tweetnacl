Require Import Tools.
Require Import notations.
Import ListNotations.

Open Scope Z.

Lemma Zlength_pos: forall A (l:list A), 0 <= Zlength l.
Proof. intros ; rewrite Zlength_correct ; go. Qed.

Lemma app_Zlength: forall (A : Type) (l l' : list A), Zlength (l ++ l') = Zlength l + Zlength l'.
Proof.
intros.
repeat rewrite Zlength_correct.
rewrite <- Nat2Z.inj_add.
rewrite app_length.
reflexivity.
Qed.

Lemma Zlength_cons' : forall (A : Type) (x : A) (l : list A), Zlength (x :: l) = (Zlength l) + 1.
Proof. intros ; rewrite Zlength_cons; omega. Qed.

Close Scope Z.