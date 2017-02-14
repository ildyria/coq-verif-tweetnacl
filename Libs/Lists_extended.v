Require Import Tweetnacl.Libs.LibTactics.
Require Import Coq.Lists.List.
Require Import stdpp.prelude.
Import ListNotations.

Lemma ListSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 <-> h1 = h2 /\ q1 = q2.
Proof. boum. Qed.

Lemma nth_drop : forall A (n:nat) (l:list A) (d: A), n < length l -> drop n l = nth n l d :: drop (S n) l.
Proof. induction n ; destr_boum l. Qed.
Arguments nth_drop [A] _ _ _ _.

(*
Lemma app_nill_r : forall (A:Type) (l:list A), l ++ nil = l.
Proof. boum. Qed.

Lemma app_nill_l : forall (A:Type) (l:list A), nil ++ l = l.
Proof. boum. Qed.

Lemma headSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 -> h1 = h2.
Proof. boum. Qed.

Lemma tailSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 -> q1 = q2.
Proof. boum. Qed.

Lemma ListSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 <-> h1 = h2 /\ q1 = q2.
Proof. boum. Qed.

Lemma length_cons : forall (A:Type) (h:A) (q:list A), length (h :: q) = S (length q).
Proof. boum. Qed.

Lemma lengthNil : forall (A:Type) (l:list A), l = nil <-> length l = 0.
Proof. ind_boum l. Qed.

Lemma consApp : forall A l (a:A), a :: l = a :: nil ++ l.
Proof. boum. Qed.

Lemma consApp2 : forall A l1 l2 (a:A), (a :: l1) ++ l2 = a :: l1 ++ l2.
Proof. boum. Qed.

Lemma consApp3 : forall A l1 l2 (a:A), l1 ++ a :: l2 = (l1 ++ a :: nil) ++ l2.
Proof. ind_boum l1. Qed.

Lemma app_assoc2 : forall (A:Type) (l1 l2 l3:list A), l1 ++ l2 ++ l3 = l1 ++ (l2 ++ l3).
Proof. boum. Qed.

Lemma list_to_length: forall A (l1 l2:list A), l1 = l2 -> length l1 = length l2.
Proof. boum. Qed.

Lemma list_eq_False : forall (A:Type) (l:list A) (a:A), a :: l = l -> False.
Proof. ind_boum l. Qed.
*)

Lemma length_pos : forall (A:Type) (l:list A), 0 <= length l.
Proof. boum. Qed.

Lemma map_drop : forall A B (f: A -> B) (l:list A) n, map f (drop n l) = drop n (map f l).
Proof. intros A B f ; induction l ; destruct n ; go. Qed.


(*
Lemma app_inv : forall A (l1 l2 l3 l4:list A), l1 = l2 -> l3 = l4 -> l1 ++ l3 = l2 ++ l4.
Proof. ind_boum l1. Qed.

Theorem appappNil: forall A (l1 l2:list A), l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof. boum. Qed.

Lemma rev_nth_error : forall A (l:list A) n, n < length l ->
    nth_error (rev l) n = nth_error l (length l - S n).
Proof.
  ind_boum l.
    simpl in H.
    simpl (rev (a::l)).
    simpl (length (a :: l) - S n).
    inversion H.
    rewrite <- minus_n_n; simpl.
    rewrite <- rev_length.
    rewrite nth_error_app2 ; go.
    rewrite <- minus_n_n; auto.
    rewrite nth_error_app1 ; go.
    rewrite (minus_plus_simpl_l_reverse (length l) n 1).
    replace (1 + length l) with (S (length l)); auto with arith.
    rewrite <- minus_Sn_m; auto with arith.
    apply IHl ; auto with arith.
    rewrite rev_length; auto.
Qed.

Lemma NoDup_rev_impl: forall A (l: list A), NoDup l -> NoDup (rev l).
Proof.
  intros A l.
  destruct l as [ | d l ] ; [intuition | ] ; generalize (d :: l) ; clear l.
  repeat match goal with
    | _ => progress omega
    | _ => progress intros
    | [ d : ?A |- @NoDup ?A ?ls ] => progress rewrite (NoDup_nth ls d)
    | [ H : context[length (rev ?l)] |- _ ] => progress rewrite rev_length in H
    | [ H : NoDup ?l |- _ ] => progress rewrite NoDup_nth in H
    | [ H : context[nth _ (rev _) _] |- _ ] => rewrite !rev_nth in H by omega
    | [ H : forall x y, _ -> _ -> nth _ _ _ = nth _ _ _ -> _, H' : nth _ _ _ = nth _ _ _ |- _ ]
    => specialize (fun pf1 pf2 => H _ _ pf1 pf2 H')
    | _ => specialize_by omega
  end.
Qed.

Lemma NoDup_rev: forall A (l:list A), NoDup l <-> NoDup (rev l).
Proof.
  split ; [| rewrite <- (rev_involutive l) at 2] ; apply NoDup_rev_impl.
Qed.

Lemma NoDup_cons_end: forall A (l:list A) x, NoDup (l ++ x::nil) -> NoDup l.
Proof.
  intros.
  apply NoDup_rev in H.
  rewrite rev_app_distr in H.
  simpl in *.
  apply NoDup_cons_iff in H.
  destruct H as [_ H].
  apply NoDup_rev in H.
  go.
Qed.

Lemma NoDup_app : forall A (l1 l2:list A), NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2.
Proof.
  repeat match goal with
    | _ => progress go
    | [ |- forall _ l1 l2, _ -> _ /\ _ ] => induction l1 as [|h q IHl]; intros l H ; simpl in *
    | [ |- _ /\ _ ] => progress split
    | [ H : _ \/ _ |- _ ] => progress destruct H
    | [ H : _ /\ _ |- _ ] => progress destruct H
    | [ H : NoDup ( _ :: _) |- _ ] => progress apply NoDup_cons_iff in H
    | [ H : NoDup (_ ++ _) |- _ ] => progress apply IHl in H
    | [ |- NoDup ( _ :: _) ] => progress apply NoDup_cons_iff
    | [ |- ~_ ] => progress intro
  end.
Qed.

Lemma nth_error_Some_Eq : forall A (l:list A) n, n < length l -> exists st, nth_error l n = Some st.
Proof. ind_boum l. destruct n ; boum. Qed.

Lemma nth_cons: forall A (h d:A) (n:nat) (q:list A), nth (S n) (h :: q) d = nth n q d.
Proof. boum. Qed.

Lemma nth_cons_0: forall A (h d:A) (q:list A), nth 0 (h :: q) d = h.
Proof. boum. Qed.

Fixpoint slice {A} (n:nat) (l:list A) : list A := match n,l with
| _,nil => nil
| 0, _ => nil
| S p, h :: q => h :: slice p q
end.

Arguments slice [A] _ _.

Lemma slice_length_or : forall A (l:list A) n, length (slice n l) = n \/ length (slice n l) = length l.
Proof. ind_boum l; destr_boum n. simpl ;  rewrite !Nat.succ_inj_wd ; go. Qed.

Lemma slice_length_nil : forall A (l:list A) n, length (slice n l) = 0 <-> l = nil \/ n = 0.
Proof. boum ; ind_boum l ; destr_boum n. Qed.

Lemma slice_length_min : forall A (l:list A) n, length (slice n l) = min n (length l).
Proof. induction l ; intros ; destruct n ; go. Qed.

Lemma slice_length_eq : forall A (l:list A)  n, length l = n -> slice n l = l.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_length_lt : forall A (l:list A)  n, length l < n -> slice n l = l.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_length_le : forall A (l:list A)  n, length l <= n -> slice n l = l.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_app : forall A (l1 l2:list A)  n m, length l1 = n -> slice (n + m) (l1 ++ l2) = l1 ++ slice m (l2).
Proof. induction l1 ; intros ; go ; destruct n ;[inv H|] ; simpl ; f_equal ; go. Qed.

Lemma slice_app_simpl_eq : forall A (l1 l2:list A)  n, length l1 = n -> slice n (l1 ++ l2) = l1.
Proof.
  intros ; assert (L1: l1 = l1 ++ slice 0 l2) by (destruct l2 ;  go).
  assert (N: n = n + 0) by go ; rewrite N ; clear N.
  rewrite L1 at 2.
  apply slice_app ; go.
Qed.

Lemma slice_app_simpl_lt : forall A (l1 l2: list A) n, length l1 > n -> slice n (l1 ++ l2) = slice n l1.
Proof.
  induction l1 ; intros.
  inversion H.
  destruct n.
  - go.
  - simpl.
    f_equal.
    apply IHl1.
    go.
Qed.

Lemma slice_cons : forall A (q:list A) h n, slice (S n) (h::q) = h :: slice n q.
Proof. go. Qed.

Lemma slice_cons' : forall A (q:list A) h n, slice (S (S n)) (h::q) = h :: slice (S n) q.
Proof. go. Qed.

Lemma slice_cons_rev : forall A (l q:list A) h n, length q = n -> slice (S n) (q ++ h :: l) = slice n q ++ h :: nil.
Proof.
  intros.
  assert(SN : S n = n + 1) by go ; rewrite SN ; clear SN.
  rewrite slice_app ; go.
  assert(SQ : slice n q = q) by (apply slice_length_eq ; go) ; rewrite SQ ; simpl ; flatten.
Qed.

Lemma slice_nil : forall A (l:list A), slice 0 l = nil.
Proof. intros ; induction l ; go. Qed.

Lemma slice_cons_0 : forall A (l:list A), slice 0 l = nil.
Proof. apply slice_nil. Qed.

Fixpoint tail {A} (n:nat) (l:list A) : list A := match n,l with
| _,nil => nil
| 0, l => l
| S p, h :: q => tail p q
end.
Arguments tail [A] _ _.

Lemma tail_cons_0 : forall A (l:list A), tail 0 l = l.
Proof. intros ; induction l ; go. Qed.

Lemma tail_cons : forall A (h:A) (q:list A) n, tail (S n) (h :: q) = tail n q.
Proof. intros ; go. Qed.


Lemma tail_length_eq : forall A (l:list A)  n, length l = n -> tail n l = [].
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma tail_length_lt : forall A (l:list A)  n, length l < n -> tail n l = [].
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma tail_length_le : forall A (l:list A)  n, length l <= n -> tail n l = [].
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_tail_app : forall A (l:list A) n, slice n l ++ tail n l = l.
Proof. induction l ; intros ; destruct n ; go. Qed.

Lemma tail_length_eq_minus : forall A (l:list A)  n, n <= length l -> length (tail n l) = length l - n.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_sliced : forall n k A (l:list A), n < k -> slice n l = slice k (slice n l).
Proof.
  induction n; intros.
  destruct l ; destruct k ; go.
  symmetry.
  apply slice_length_le.
  rewrite slice_length_min.
  assert(SN : (S n) < (length l) \/ (S n)  = (length l) \/ (S n) > (length l)) by go.
  destruct SN ; [|destruct H0].
  rewrite min_l ; go.
  rewrite min_l ; go.
  rewrite min_r ; go.
Qed.

Lemma map_slice : forall A B (f: A -> B) (l:list A) n, map f (slice n l) = slice n (map f l).
Proof.
  intros A B f.
  induction l ; destruct n ; go.
Qed.

Lemma map_tail : forall A B (f: A -> B) (l:list A) n, map f (tail n l) = tail n (map f l).
Proof.
  intros A B f.
  induction l ; destruct n ; go.
Qed.
*)


Open Scope Z.

Lemma Zlength_pos: forall {A : Type} (l:list A), 0 <= Zlength l.
Proof. intros ; rewrite Zlength_correct ; go. Qed.

Lemma app_Zlength: forall {A : Type} (l l' : list A), Zlength (l ++ l') = Zlength l + Zlength l'.
Proof.
intros.
repeat rewrite Zlength_correct.
rewrite <- Nat2Z.inj_add.
rewrite app_length.
reflexivity.
Qed.

Lemma Zlength_cons' : forall {A : Type} (x : A) (l : list A), Zlength (x :: l) = (Zlength l) + 1.
Proof. intros ; rewrite Zlength_cons; omega. Qed.

Lemma Zlength_map: forall A B (f: A -> B) l, Zlength (map f l) = Zlength l.
Proof. intros; induction l ; auto ; rewrite map_cons ; repeat rewrite Zlength_cons ; go. Qed.

Close Scope Z.