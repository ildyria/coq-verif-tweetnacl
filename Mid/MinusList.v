Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import stdpp.prelude.
Import ListNotations.

Open Scope Z.

(* Some definitions relating to the functional spec of this particular program.  *)
Fixpoint ZminusList (l : list Z) : list Z := match l with
| [] => []
| h :: q => (-h) :: ZminusList q
end.

Lemma ZminusList_cons: forall h q, ZminusList (h :: q) = -h :: ZminusList q.
Proof. go. Qed.

Lemma ZminusList_app: forall l1 l2, ZminusList (l1 ++ l2) = (ZminusList l1) ++ (ZminusList l2).
Proof. elim; go. Qed.

Lemma ZminusList_length: forall l, length (ZminusList l) = length l.
Proof. elim; go. Qed.

Lemma ZminusList_Zlength: forall l, Zlength (ZminusList l) = Zlength l.
Proof. convert_length_to_Zlength ZminusList_length. Qed.

Lemma ZminusList_nil: forall l, ZminusList l = [] <-> l = [].
Proof. elim ; go. Qed.

Lemma ZminusList_ZofList: forall n l, ZofList n (ZminusList l) = - ZofList n l.
Proof. move=> n ; elim=> [|h l IHl] ; intros ; go ; simpl; rewrite IHl; lia. Qed.

Close Scope Z.