Require Import stdpp.list.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.ZofList.
From Tweetnacl Require Import ListsOp.Forall_ZofList.
Open Scope Z.

Section Integer.

Variable n:Z.
Hypothesis Hn: n > 0.

Fixpoint ListofZn_fp (a:Z) (fuel:nat) : list Z :=
match fuel with 
  | 0%nat => []
  | S fuel => (a mod 2^n) :: ListofZn_fp (a/2^n) fuel
end.

Definition ListofZ16 (a:Z) : list Z := ListofZn_fp a 16.

Lemma ListofZ16_length : forall (a:Z), length (ListofZ16 a) = 16%nat.
Proof. done. Qed.

Definition ListofZ32 (a:Z) : list Z := ListofZn_fp a 32.

Lemma ListofZ32_length : forall (a:Z), length (ListofZ32 a) = 32%nat.
Proof. done. Qed.

Local Lemma next_ : forall a b, 0 <= a /\ a < 2^n -> (a + 2 ^ n * b) `div` 2 ^ n = b.
Proof.
  move => a b Ha.
  have Hn':= pown0 n Hn.
  rewrite Z.mul_comm.
  orewrite Z_div_plus_full.
  rewrite Zdiv_small => //.
Qed.

Lemma ListofZ16_ZofList_length: forall (l:list Z) (a:Z),
  Forall (fun x => 0 <= x < 2^n) l ->
  (length l = 16)%nat ->
  ZofList n l = a ->
  ListofZ16 a = l.
Proof.
  move => l a Hlbound HlLength.
  repeat (destruct l ; tryfalse).
  repeat match goal with
    | [ H: Forall _ _ |- _ ] => apply Forall_cons_1 in H ; destruct H
  end.
  rewrite /ListofZ16.
  move => <-.
  simpl.
  repeat match goal with
    | [ |- _ :: _ = _ :: _ ] => f_equal
    | _ => rewrite next_ => //
    | _ => rewrite Z.mul_comm Z_mod_plus_full
    | _ => apply Z.mod_small => //
  end.
Qed.

Lemma ListofZ32_ZofList_impl_length: forall (l:list Z) (a:Z),
  Forall (fun x => 0 <= x < 2^n) l ->
  (length l = 32)%nat ->
  ZofList n l = a ->
  ListofZ32 a = l.
Proof.
  move => l a Hlbound HlLength.
  repeat (destruct l ; tryfalse).
  repeat match goal with
    | [ H: Forall _ _ |- _ ] => apply Forall_cons_1 in H ; destruct H
  end.
  rewrite /ListofZ32.
  move => <-.
  simpl.
  repeat match goal with
    | [ |- _ :: _ = _ :: _ ] => f_equal
    | _ => rewrite next_ => //
    | _ => rewrite Z.mul_comm Z_mod_plus_full
    | _ => apply Z.mod_small => //
  end.
Qed.

Lemma ListofZ32_ZofList_length: forall (l:list Z),
  Forall (fun x => 0 <= x < 2^n) l ->
  (length l = 32)%nat ->
  ListofZ32 (ZofList n l) = l.
Proof.
  move => l Hl Hll.
  apply ListofZ32_ZofList_impl_length => //.
Qed.

Lemma ListofZ32_ZofList_Zlength: forall (l:list Z),
  Forall (fun x => 0 <= x < 2^n) l ->
  Zlength l = 32 ->
  ListofZ32 (ZofList n l) = l.
Proof. convert_length_to_Zlength ListofZ32_ZofList_length. Qed.

End Integer.

Close Scope Z.
