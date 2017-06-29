Require Import Tweetnacl.Libs.Export.
Require Import stdpp.prelude.

Open Scope Z.

(* Some definitions relating to the functional spec of this particular program.  *)
Definition list_cswap (b:Z) (p q : list Z) : list Z := 
  if (Z.eqb b 0) then
    p
  else q.

Lemma list_cswap_nth_true: forall i d p q,
  nth i (list_cswap 1 p q) d = nth i q d.
Proof.
  intros. go.
Qed.

Lemma list_cswap_nth_false: forall i d p q,
  nth i (list_cswap 0 p q) d = nth i p d.
Proof.
  intros. go.
Qed.

Close Scope Z.