Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import stdpp.prelude.
Import ListNotations.

Open Scope Z.

Fixpoint ZscalarMult (a:Z) (b:list Z) : list Z := match b with
| [] => []
| h :: q => a * h :: ZscalarMult a q
end.

Notation "A ∘∘ B" := (ZscalarMult A B) (at level 60, right associativity).

Lemma ZscalarMultnil : forall n, n ∘∘ [] = [].
Proof. go. Qed.

Lemma ZscalarMult_eq_ZunopList : forall a (b : list Z), ZscalarMult a b = ZunopList Z.mul a b.
Proof. induction b ; go. Qed.

Lemma ZscalarMult_length: forall n l, length (n ∘∘ l) = length l.
Proof. intro n ; induction l ; go. Qed.

Lemma ZscalarMult_Zlength: forall n l, Zlength (n ∘∘ l) = Zlength l.
Proof. convert_length_to_Zlength ZscalarMult_length. Qed.


Lemma ZscalarMult_take: forall l n m, take n (m ∘∘ l) = m ∘∘ (take n l).
Proof. induction l ; intros [] m; go. Qed.

Lemma ZscalarMult_drop: forall l n m, drop n (m ∘∘ l) = m ∘∘ (drop n l).
Proof. induction l ; intros [] m; go. Qed.

(* ADD PROOF x * nth L = nth (x * L) *)
Lemma ZscalarMult_nth: forall l i k d, k * nth i l d = nth i (k ∘∘ l) (k * d).
Proof. induction l ; intros ; simpl ; flatten ; go. Qed.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Notation "ℤ.lst A" := (ZofList n A) (at level 65, right associativity).

Lemma ZscalarMult_correct: forall a b, ℤ.lst a ∘∘ b = a * ℤ.lst b.
Proof.
  intros a ; induction b ; go.
  unfold ZscalarMult ; fold ZscalarMult.
  rewrite! ZofList_cons.
  rewrite IHb.
  ring.
Qed.

End Integer.

Lemma ZscalarMult_bound_const: forall (m2 n2 o p a: Z) (b: list Z),
  0 <= a ->
  Forall (fun x => m2 <= x <= n2) b -> 
  o = a * m2 ->
  p = a * n2 ->
  Forall (fun x => o <= x <= p) (a ∘∘ b).
Proof.
  introv Ha Hb Ho Hp.
  rewrite ZscalarMult_eq_ZunopList.
  eapply (Forall_ZunopList _ (fun x : ℤ => a = x) (fun x : ℤ => m2 <= x <= n2)) ; go.
Qed.


Close Scope Z.
