Require Import Tweetnacl.Libs.Export.

Open Scope Z.

(* Some definitions relating to the functional spec of this particular program.  *)
Definition list_cswap (b:Z) (p q : list Z) : list Z := 
  if (Z.eqb b 0) then
    p
  else q.

Lemma list_cswap_nth_true: forall i d p q,
  nth i (list_cswap 1 p q) d = nth i q d.
Proof. go. Qed.

Lemma list_cswap_nth_false: forall i d p q,
  nth i (list_cswap 0 p q) d = nth i p d.
Proof. go. Qed.

Lemma list_cswap_length_eq: forall b p q, length p = length q -> length p = length (list_cswap b p q).
Proof. intros; unfold list_cswap; destruct (Z.eqb b 0); go. Qed.

Lemma list_cswap_Zlength_eq: forall b p q, Zlength p = Zlength q -> Zlength p = Zlength (list_cswap b p q).
Proof. intros; unfold list_cswap; destruct (Z.eqb b 0); go. Qed.

Close Scope Z.

Definition Sel25519 b p q := list_cswap b p q.