Require Export Libs.

Set Implicit Arguments.

(* Iterative tools *)
Section All.
  Variable T : Type.
  Variable T1 : Type.
  Variable T2 : Type.


  Fixpoint All (o: T -> T1 -> T1) (d:T1) (ls:list T) : T1 := match ls with
    | nil => d
    | h :: q => o h (All o d q)
  end.
End All.

Section AllApp.
  Variable T : Type.
  Variable T2 : Type.
  Variable P : T -> Prop.
  Variable V : T -> nat.
  Variable V2 : T -> T2.
  Variable LS : T -> list T2.

  Definition orAll (ls:list Prop): Prop := 
    All or False ls.

  Definition andAll (ls: list Prop): Prop :=
    All and True ls.

  Definition SumAll (ls:list nat) : nat :=
    All plus 0 ls.

  Definition MaxAll (ls:list nat) : nat :=
    All max 0 ls.

  Inductive orderedList : list nat -> Prop := 
    | NilOrdered         : orderedList nil
    | SingletonOrdered n : orderedList (n::nil)
    | ConOrdered a h q
      (ORDER: a < h)
      (ORDERED: orderedList (h::q))
      : (* ===================== *)
      orderedList (a::h::q).
End AllApp.

(* Lists Tools *)
Lemma app_nill_r : forall (A:Type) (l:list A), l ++ nil = l.
Proof. go. Qed.

Lemma app_nill_l : forall (A:Type) (l:list A), nil ++ l = l.
Proof. go. Qed.

Lemma headSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 -> h1 = h2.
Proof. go. Qed.

Lemma tailSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 -> q1 = q2.
Proof. go. Qed.

Lemma lengthNil : forall (A:Type) (l:list A), l = nil <-> length l = 0.
Proof. intros. split ; intro ; induction l ; go. Qed.

Lemma consApp : forall A l (a:A), a :: l = a :: nil ++ l.
Proof. go. Qed.

Lemma consApp2 : forall A l1 l2 (a:A), (a :: l1) ++ l2 = a :: l1 ++ l2.
Proof. go. Qed.

Lemma consApp3 : forall A l1 l2 (a:A), l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof. go. Qed.

Lemma app_assoc2 : forall (A:Type) (l1 l2 l3:list A), l1 ++ l2 ++ l3 = l1 ++ (l2 ++ l3).
Proof. go. Qed.

Lemma list_eq_False : forall (A:Type) (l:list A) (a:A), a :: l = l -> False.
Proof.
dependent induction l.
intros.
inversion H.
intros.
inversion H.
eapply IHl.
eauto.
Qed.

Lemma app_inv : forall A (l1 l2 l3 l4:list A), l1 = l2 -> l3 = l4 -> l1 ++ l3 = l2 ++ l4.
Proof.
induction l1 ; destruct l2 ; intros ; go.
Qed.

Lemma orderedCon : forall l a, orderedList (a :: l) -> orderedList l.
Proof. intros ; dependent induction H ; go. Qed.

Lemma orderedConcat : forall l1 l2, orderedList (l1 ++ l2) -> orderedList l1 /\ orderedList l2.
Proof.
intros.
split.
- dependent induction l1.
  + go.
  + dependent induction l1.
  * go.
  * apply ConOrdered.
      inv H ; go.
      apply IHl0 with l2.
      apply orderedCon with a.
      go.
- induction l1.
  + go.
  + apply IHl1.
    apply orderedCon with a.
    go.
Qed.

Lemma rev_nth_error : forall A (l:list A) n, n < length l ->
    nth_error (rev l) n = nth_error l (length l - S n).
Proof.
induction l.
- intros.
  inversion H.
- intros.
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

Lemma NoDup_rev: forall A (l:list A), NoDup l <-> NoDup (rev l).
Proof.
intros A l.
destruct l as [ | d l ] ; [intuition | ] ; generalize (d :: l) ; clear l.
split ; intro.
- rewrite NoDup_nth.
  intros i j IL IJ Nths.
  rewrite rev_length in IL.
  rewrite rev_length in IJ.
  rewrite NoDup_nth in H.
  specialize H with (length l - S i) (length l - S j).
  assert(HI: length l - S i < length l) by omega.
  assert(HJ: length l - S j < length l) by omega.
  apply H in HI ; go.
  rewrite !rev_nth in Nths ; eauto.
- rewrite NoDup_nth.
  intros i j IL IJ Nths.
  rewrite NoDup_nth in H.
  rewrite !rev_length in H.
  specialize H with (length l - S i) (length l - S j).
  assert(HI: length l - S i < length l) by omega.
  assert(HJ: length l - S j < length l) by omega.
  apply H in HI.
  omega.
  omega.
  rewrite !rev_nth ; go.
  assert(HI' : length l - S (length l - S i) = i) by omega.
  assert(HJ' : length l - S (length l - S j) = j) by omega.
  rewrite HI'.
  rewrite HJ'.
  apply Nths.
  Unshelve.
  apply d.
  Unshelve.
  apply d.
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
induction l1 ; intros ; simpl in *.
split ; go.
apply NoDup_cons_iff in H.
destruct H.
apply IHl1 in H0.
destruct H0.
split ; go.
apply NoDup_cons_iff.
split ; go.
intros H'.
apply H.
apply in_or_app.
go.
Qed.

Fixpoint beq_listnat l1 l2 := match (l1,l2) with
| (nil, nil) => true
| (h1 :: q1, h2 :: q2) => (beq_nat h1 h2) && (beq_listnat q1 q2) 
| _ => false
end.

Fact listEqRefl : forall l, beq_listnat l l = true.
Proof.
induction l ; go.
apply andb_true_iff ; split ; go ; rewrite beq_nat_refl with a; go.
Qed.

(* props*)
Lemma orFalse : forall (P:Prop), P \/ False <-> P.
Proof. intros ; split ; intro ; [destruct H|] ; go. Qed.

Lemma Falseor : forall (P:Prop), False \/ P <-> P.
Proof. intros ; split ; intro ; [destruct H|] ; go. Qed.

Lemma andTrue : forall (P:Prop), P /\ True <-> P.
Proof. intros ; split ; intro; [destruct H|] ; go. Qed.

Lemma Trueand : forall (P:Prop), True /\ P <-> P.
Proof. intros ; split ; intro; [destruct H|] ; go. Qed.

Theorem GaussSum: forall a b c, a + c = b + c <-> a = b.
Proof. intros ; split ; intros ; omega. Qed.

(* Tupples *)

Lemma tupple_eq : forall A B (x1 x2:A) (y1 y2:B), (x1,y1) = (x2,y2) <->
(x1 = x2 /\ y1 = y2).
Proof. intros ; split ; intro ; go ; destruct H as [Hx Hy] ; go. Qed.

Theorem consconsNil: forall A (l1 l2:list A), l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof. go. Qed.

Fact flat_map_map X Y Z (f : Y -> list Z) (g : X -> Y) l : 
   flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l; simpl; f_equal; auto. Qed.

Fact flat_map_distr Y Z (f : Y -> list Z)  l1 l2 : 
   flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof. induction l1 ; go ; simpl ; rewrite IHl1 ; go. Qed.

Fact flat_map_ext X Y (f g : X -> list Y) l :
   (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof. induction l; simpl; intro; f_equal; auto. Qed.

Fact map_ext X Y (f g : X -> Y) l :
   (forall x, In x l -> f x = g x) -> map f l = map g l.
Proof. induction l; simpl; intro; f_equal; auto. Qed.


Lemma sumAllapp : forall (h:nat) (q:list nat), SumAll (h::q) = h + SumAll q.
Proof. intros ; induction q ; go. Qed.

Theorem SomeEq: forall A (a b:A), Some a = Some b <-> a = b.
Proof. go. Qed.

Lemma nth_error_Some_Eq : forall A (l:list A) n, n < length l -> exists st, nth_error l n = Some st.
Proof. induction l ; intros ; go ; destruct n ; [exists a|apply IHl] ; go. Qed.

Fixpoint slice A (n:nat) (l:list A) : list A := match n,l with
| _,nil => nil
| 0, _ => nil
| S p, h :: q => h :: slice p q
end.

Lemma slice_length_or : forall A (l:list A) n, length (slice n l) = n \/ length (slice n l) = length l.
Proof.
induction l ; intros ; destruct n ; go ; simpl ; rewrite !Nat.succ_inj_wd ; go.
(*  Search(S _ = S _ <-> _ = _).*)
Qed.

Lemma slice_length_nil : forall A (l:list A) n, length (slice n l) = 0 <-> l = nil \/ n = 0.
Proof.
intros ; split.
- induction l ; intro ; go ; destruct n ; go.
- intro ; destruct H ; subst ; [destruct n | destruct l] ; go.
Qed.

Lemma slice_length_min : forall A (l:list A) n, length (slice n l) = min n (length l).
Proof. induction l ; intros ; destruct n ; go. Qed.

Lemma slice_length_eq : forall A (l:list A)  n, length l = n -> slice n l = l.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_length_lt : forall A (l:list A)  n, length l < n -> slice n l = l.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_length_le : forall A (l:list A)  n, length l <= n -> slice n l = l.
Proof. induction l ; intros ; destruct n ; simpl ; f_equal ; go. Qed.

Lemma slice_app : forall A (l1 l2:list A)  n m, length l1 = n -> slice (n + m) (l1 ++ l2) = l1 ++ slice m (l2).
Proof.
induction l1 ; intros ; go ; destruct n.
- inv H.
- simpl ; f_equal ; go.
Qed.

Lemma slice_app_simpl_eq : forall A (l1 l2:list A)  n, length l1 = n -> slice n (l1 ++ l2) = l1.
Proof.
intros ; assert (L1: l1 = l1 ++ slice 0 l2) by (destruct l2 ;  go).
assert (N: n = n + 0) by go ; rewrite N.
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

Lemma slice_cons : forall A (q:list A) h n, slice (S (S n)) (h::q) = h :: slice (S n) q.
Proof. go. Qed.

Lemma slice_cons_rev : forall A (l q:list A) h n, length q = n -> slice (S n) (q ++ h :: l) = slice n q ++ h :: nil.
Proof.
intros.
assert(SN : S n = n + 1) by go ; rewrite SN.
rewrite slice_app ; go.
assert(SQ : slice n q = q) by (apply slice_length_eq ; go) ; rewrite SQ ; simpl ; flatten.
Qed.

Lemma slice_nil : forall A (l:list A), slice 0 l = nil.
Proof.
intros.
induction l ; go.
Qed.

Fixpoint tail A (n:nat) (l:list A) : list A := match n,l with
| _,nil => nil
| 0, l => l
| S p, h :: q => tail p q
end.

Lemma slice_tail_app : forall A (l:list A) n, slice n l ++ tail n l = l.
Proof. induction l ; intros ; destruct n ; go. Qed.

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

Definition oList A (o:A -> A -> Prop) (m:A) (l:list A) := In m l -> forall m', In m' l -> o m m'.

Lemma map_slice : forall A B (f: A -> B) n (l:list A), map f (slice n l) = slice n (map f l).
Proof.
intros A B f n l.
induction l using rev_ind.
- destruct n ; go.
- assert(HnL: length l < n \/ length l = n \/ length l > n) by go.
destruct HnL ; [|destruct H].
  + rewrite map_app.
    assert(LM : length (map f l) = length l) by apply map_length.
    assert(length l + 1 = n \/ length l + 1 < n).
    omega.
    destruct H0.
    assert(HLEFT : slice n (l ++ x :: nil) = l ++ slice 1 (x :: nil)).
    {
    rewrite <- H0.
    apply slice_app; go.
    }
    assert(HRIGHT : slice n (map f l ++ map f (x :: nil)) = map f l ++ slice 1 (map f (x :: nil))).
    {
    rewrite <- H0.
    apply slice_app ; go.
    }
    rewrite HLEFT.
    rewrite HRIGHT.
    rewrite map_app.
    go.
    assert(Hm : exists m, n = (length l + m + 1)) by (exists (n - (length l + 1)) ; go).
    destruct Hm as [m Hm].
    assert(HLEFT : slice n (l ++ x :: nil) = l ++ slice (m + 1) (x :: nil)).
    {
    rewrite Hm.
    rewrite plus_assoc_reverse.
    apply slice_app ; go.
    }
    assert(HRIGHT : slice n (map f l ++ map f (x :: nil)) = map f l ++ slice (m + 1) (map f (x :: nil))).
    {
    rewrite Hm.
    rewrite plus_assoc_reverse.
    apply slice_app ; go.
    }
    rewrite HLEFT.
    rewrite HRIGHT.
    rewrite map_app.
    simpl.
    destruct m ; go.
    assert(SSM : S m + 1 = S (S m)) by go.
    rewrite SSM.
    rewrite !slice_cons.
    go.
  + rewrite map_app.
    assert(LM : length (map f l) = length l) by apply map_length.
    assert(LLM: length l = n) by go.
    eapply slice_app_simpl_eq in H.
    rewrite LLM in LM.
    eapply slice_app_simpl_eq in LM.
    rewrite H.
    rewrite LM.
    go.
  + assert(exists l1 l2, l ++ x:: nil = l1 ++ l2 /\ length l1 = n /\ l1 = slice n l).
    {
    exists (slice n (l ++ x :: nil)).
    exists (tail n (l ++ x :: nil)).
    split.
    symmetry.
    apply slice_tail_app.
    split.
    rewrite slice_length_min.
    apply Min.min_l.
    rewrite app_length.
    go.
    apply slice_app_simpl_lt.
    go.
    }
    destruct H0 as [l1 H0].
    destruct H0 as [l2 H0].
    destruct H0 as [Hl2 H0].
    destruct H0 as [Hln1 Hl1]. 
    assert(exists l1 l2, map f (l ++ x:: nil) = l1 ++ l2 /\ length l1 = n /\ l1 = slice n (map f l)).
    {
    exists (slice n (map f (l ++ x:: nil))).
    exists (tail n (map f (l ++ x:: nil))).
    split.
    symmetry.
    apply slice_tail_app.
    rewrite slice_length_min.
    split.
    apply Min.min_l.
    rewrite map_length.
    rewrite app_length.
    go.
    rewrite map_app.
    apply slice_app_simpl_lt.
    assert(MAPEQ: length (map f l) = length l) by apply map_length.
    rewrite <- MAPEQ in H.
    go.
    }
    destruct H0 as [l3 H0].
    destruct H0 as [l4 H0].
    destruct H0 as [Hl4 H0].
    destruct H0 as [Hln3 Hl3].
    rewrite Hl2 at 1. rewrite Hl4.
    rewrite (plus_n_O n).
    rewrite slice_app ; go.
    rewrite slice_app ; go.
    rewrite !slice_nil.
    rewrite !app_nil_r.
    subst l3.
    subst l1.
    apply IHl.
Qed.

Lemma truefalseImplFalse : false = true <-> False.
Proof.
split; go.
Qed.