Require Import stdpp.prelude.
Require Import ssreflect.
From Tweetnacl Require Import Libs.Export.
Require Import Recdef.

Local Open Scope Z.
Definition local_update_M (j:nat) (a:Z) (b : list Z) (x:Z) := a * ( from_option id 0 (b !! j)) + x.
Definition update_M_i_j (i j a:Z) (b:list Z) (o:list Z) := alter (local_update_M (Z.to_nat j) a b) (Z.to_nat (i + j)) o.
Definition update_M_i_j' (i j:nat) (a:Z) (b:list Z) (o:list Z) : (list Z) := alter (local_update_M j a b) (i + j)%nat o.

Function inner_M_fix (i j a:Z) (b o : list Z) {measure Z.to_nat j} : list Z :=
  if (j <=? 0) then o else inner_M_fix i (j - 1) a b (update_M_i_j i (j - 1) a b o).
Proof. intros. apply Z2Nat.inj_lt ; move: teq; rewrite Z.leb_gt => teq; omega. Defined.

Fixpoint inner_M_fix' (i j : nat) (a:Z) (b o : list Z) := match j with
  | 0%nat => o
  | S p => inner_M_fix' i p a b (update_M_i_j' i p a b o)
end.

Function inner_M_fix'' (i j a:Z) (b o : list Z) {measure Z.to_nat j} : list Z :=
  if (j <=? 0) then o else update_M_i_j i (j - 1) a b (inner_M_fix'' i (j - 1) a b o).
Proof. intros. apply Z2Nat.inj_lt ; move: teq; rewrite Z.leb_gt => teq; omega. Qed.

Lemma update_M_i_j_eq : forall (i j a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
    update_M_i_j i j a b o = update_M_i_j' (Z.to_nat i) (Z.to_nat j) a b o.
Proof.
  intros ; unfold update_M_i_j, update_M_i_j', alter; f_equal ; rewrite Z2Nat.inj_add; omega.
Qed.

Lemma update_M_i_j_comm_j: forall (i j k:nat) (a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
  0 <= k ->
  j <> k -> 
    update_M_i_j' i j a b (update_M_i_j' i k a b o) = update_M_i_j' i k a b (update_M_i_j' i j a b o).
Proof.
repeat match goal with
  | _ => omega
  | _ => progress intro
  | _ => progress unfold update_M_i_j'
  | _ => apply list_alter_commute ; intro
end.
Qed.

Lemma inner_M_i_j_eq : forall (i j a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
    inner_M_fix i j a b o = inner_M_fix' (Z.to_nat i) (Z.to_nat j) a b o.
Proof.
  intros i j a b o Hi Hj ; gen b o.
  apply (natlike_ind (fun j => ∀ b o : list ℤ, inner_M_fix i j a b o = inner_M_fix' (Z.to_nat i) (Z.to_nat j) a b o)) ; try omega.
  intros ; rewrite inner_M_fix_equation ; auto.
  clear Hj j ; intros j Hj iHj b o.
  change (Z.succ j) with (j + 1); replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)).
  2: rewrite Z2Nat.inj_add ; change (Z.to_nat 1) with 1%nat ; omega.
  rewrite inner_M_fix_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  replace (j + 1 - 1) with j by omega.
  rewrite iHj ; rewrite update_M_i_j_eq ; go.
Qed.

Lemma inner_M_fix''_com: forall (i j k a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
  j <= k ->
    update_M_i_j i k a b (inner_M_fix'' i j a b o) = inner_M_fix'' i j a b (update_M_i_j i k a b o).
Proof.
  intros i j k a b o Hi Hj Hk.
  gen k b o.
  apply (natlike_ind (fun j => ∀ k : ℤ, j <= k -> ∀ b o : list ℤ, update_M_i_j i k a b (inner_M_fix'' i j a b o) =
      inner_M_fix'' i j a b (update_M_i_j i k a b o))) ; try omega.
  - intros ; rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation ; auto.
  - clear Hj j ; intros j Hj iHj k Hk b o ; sort.
    change (Z.succ j) with (j + 1) in *.
    rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation.
    flatten.
    replace (j + 1 - 1) with (j) by omega.
    rewrite <- iHj by omega.
    rewrite ?update_M_i_j_eq ; try omega.
    rewrite update_M_i_j_comm_j ; go.
    intro ; apply Z2Nat.inj_iff in H ; omega.
Qed.

Lemma inner_M_i_j_eq'' : forall (i j a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
    inner_M_fix i j a b o = inner_M_fix'' i j a b o.
Proof.
  intros i j a b o Hi Hj.
  gen b o.
  apply (natlike_ind (fun j => ∀ b o : list ℤ, inner_M_fix i j a b o = inner_M_fix'' i j a b o)) ; try omega.
  - intros ; rewrite inner_M_fix_equation ; rewrite inner_M_fix''_equation ; auto.
  - clear Hj j => j Hj iHj b o ; sort.
    change (Z.succ j) with (j + 1).
    rewrite inner_M_fix_equation ; rewrite inner_M_fix''_equation.
    flatten.
    oreplace (j + 1 - 1) (j).
    rewrite iHj.
    rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation.
    flatten.
    apply Z.leb_gt in Eq0.
    rewrite <- inner_M_fix''_com by omega.
    rewrite ?update_M_i_j_eq ; try omega.
    rewrite update_M_i_j_comm_j ; go.
    intro ; apply Z2Nat.inj_iff in H ; omega.
Qed.

Lemma inner_M_fix_0 : forall i a b o, 0 <= i -> inner_M_fix i 0 a b o = o.
Proof. intros ; rewrite inner_M_fix_equation ; flatten ; compute in Eq ; tryfalse. Qed.

Lemma inner_M_fix_step j : 0 <= j -> forall i a b o, 0 <= i -> inner_M_fix i (j + 1) a b o = update_M_i_j i j a b (inner_M_fix i j a b o).
Proof.
  intros.
  rewrite inner_M_i_j_eq'' ; try omega.
  rewrite inner_M_fix''_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  oreplace (j + 1 - 1)  (j).
  rewrite inner_M_i_j_eq''; go.
Qed.

Lemma inner_M_fix_length : forall i j a b o, 0 <= j -> length (inner_M_fix i j a b o) = length o.
Proof.
  intros i j a b o Hj; gen i a b o .
  apply (natlike_ind (fun j => ∀ (i a : ℤ) (b o : list ℤ), length (inner_M_fix i j a b o) = length o)) ; try omega.
  intros ; rewrite inner_M_fix_equation ; go.
  clear j Hj; intros j Hj iHj i a b o.
  change (Z.succ j) with (j + 1).
  rewrite inner_M_fix_equation.
  destruct (j + 1 <=? 0) ; auto.
  replace (j + 1 - 1) with (j) by omega.
  rewrite iHj.
  unfold update_M_i_j.
  rewrite alter_length.
  reflexivity.
Qed.

Lemma inner_M_fix_Zlength : forall i j a b o, 0 <= j -> Zlength (inner_M_fix i j a b o) = Zlength o.
Proof. convert_length_to_Zlength inner_M_fix_length. Qed.

Lemma inner_M_fix_app_take : forall i j a b o, 0 <= j -> 0 <= i -> i <= length o -> inner_M_fix i j a b o = take (Z.to_nat i) o ++ drop (Z.to_nat i) (inner_M_fix i j a b o).
Proof.
intros i j a b o Hj Hi. gen i a b o.
eapply (natlike_ind (fun j => ∀ i : ℤ, 0 ≤ i → ∀ (a : ℤ) (b o : list ℤ),
  i ≤ length o → inner_M_fix i j a b o = take (Z.to_nat i) o ++ drop (Z.to_nat i) (inner_M_fix i j a b o))) ; try omega.
intros; rewrite inner_M_fix_0 ; try omega; rewrite take_drop; reflexivity.
clear j Hj => j Hj iHj i Hi a b o Ho.
change (Z.succ j) with (j + 1).
rewrite inner_M_i_j_eq''; try omega.
rewrite inner_M_fix''_equation.
flatten.
rewrite take_drop; reflexivity.
oreplace (j + 1 - 1) j.
rewrite <- inner_M_i_j_eq'' ; try omega.
rewrite iHj ; try omega.
unfold update_M_i_j.
rewrite alter_app_r_alt.
f_equal.

Focus 2.
rewrite take_length ; rewrite Z2Nat.inj_add ; try omega.
apply (NPeano.Nat.le_trans _ (Z.to_nat i)) ; try omega.
apply Min.le_min_l.

rewrite drop_app_ge. 2: (rewrite take_length ; apply Min.le_min_l).
replace ((Z.to_nat i - length (take (Z.to_nat i) o)))%nat with 0%nat.
reflexivity.
rewrite take_length min_l ; go.
rewrite <- Nat2Z.id ; apply Z2Nat.inj_le ; go.
Qed.

Lemma inner_M_fix_app : forall i j a b o o', 0 <= j -> 0 <= i -> i + j <= length o -> inner_M_fix i j a b (o ++ o') = (inner_M_fix i j a b o) ++ o'.
Proof.
intros i j a b o o'; gen i j a b o'; induction o as [ | h o iHo] using rev_ind.
- intros. simpl in *.
replace i with 0 ; replace j with 0 ; subst ; repeat rewrite inner_M_fix_0 ; go.
- intros i j a b o' Hj Hi. gen i a b o'.
  apply (natlike_ind (fun j => ∀ i : ℤ, 0 ≤ i → ∀ (a : ℤ) (b o' : list ℤ),
  i + j <= length (o ++ [h]) → inner_M_fix i j a b ((o ++ [h]) ++ o') = inner_M_fix i j a b (o ++ [h]) ++ o')) ; try omega.
  intros.
  repeat (rewrite inner_M_fix_0 ; try omega) ; reflexivity.
  clear j Hj; intros j Hj iHj i Hi a b o' Hijo.
  change (Z.succ j) with (j + 1).
  repeat (rewrite inner_M_i_j_eq'' ; try omega).
  rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation.
  flatten.
  replace (j + 1 - 1) with j by omega.
  repeat (rewrite <- inner_M_i_j_eq'' ; try omega).
  change (Z.succ j) with (j + 1) in *.
  assert(Hijo': i + j <= length o) by (rewrite app_length in Hijo ; simpl in Hijo ; lia).
  clear Hijo.
  unfold update_M_i_j.
  rewrite <- alter_app_l.
  f_equal.
  rewrite -app_assoc -cons_middle iHo ; try omega.
  rewrite iHo ; try omega.
  rewrite app_assoc_reverse cons_middle.
  reflexivity.
  rewrite inner_M_fix_length ; try omega.
  rewrite app_length.
  rewrite <- Nat2Z.id.
  simpl.
  apply Z2Nat.inj_lt ; lia.
Qed.

Lemma inner_M_fix_take : forall i j a b o, 0 <= j -> 0 <= i -> i + j <= length o -> (inner_M_fix i j a b (take (Z.to_nat (i + j))  o)) = take (Z.to_nat (i + j)) (inner_M_fix i j a b o).
Proof.
  intros.
  symmetry.
  rewrite <- (take_drop (Z.to_nat (i + j)) o).
  rewrite inner_M_fix_app ; try omega.
  rewrite (take_drop (Z.to_nat (i + j)) o).
  2: rewrite take_length Nat2Z.inj_min Z.min_l Z2Nat.id ; omega.
  rewrite take_app_ge.
  2: rewrite inner_M_fix_length ; try omega ; rewrite take_length ; apply Min.le_min_l.
  rewrite inner_M_fix_length ; try omega.
  rewrite take_length min_l.
  2: rewrite <- Nat2Z.id; apply Z2Nat.inj_le; omega.
  replace ((Z.to_nat (i + j) - Z.to_nat (i + j))%nat) with 0%nat by omega.
  replace (take 0 (drop (Z.to_nat (i + j)) o)) with (nil:list Z) by reflexivity.
  rewrite app_nil_r ; auto.
Qed.

Lemma inner_M_fix_app_drop : forall i j a b o, 0 <= j -> 0 <= i -> inner_M_fix i j a b o = take (Z.to_nat (i + j)) (inner_M_fix i j a b o) ++ drop (Z.to_nat (i + j)) o.
Proof.
  intros i j a b o Hj Hi.
  rewrite <- (take_drop (Z.to_nat (i + j)) o) at 1.
  assert(i + j <= length o \/ i + j > length o) by omega.
  destruct H.
  - rewrite inner_M_fix_app ; try omega.
    2: rewrite take_length; rewrite min_l.
    2: rewrite Z2Nat.id ; omega.
    2: move : H ; rewrite Z2Nat.inj_le ; try omega ; rewrite (Nat2Z.id (length o)) => H ; omega.
    rewrite inner_M_fix_take ; try omega ; reflexivity.
  - 
  repeat match goal with
    | _ => reflexivity
    | _ => rewrite drop_ge
    | _ => rewrite take_ge
    | _ => rewrite app_nil_r
    | _ => rewrite inner_M_fix_length ; try omega
  end ;
  apply Z.gt_lt_iff in H ; move: H ; rewrite Z2Nat.inj_lt ; try omega ; rewrite (Nat2Z.id (length o)) => H ; omega.
Qed.

Lemma inner_M_fix'_app_drop : forall i j a b o, inner_M_fix' i j a b o = take (i + j)%nat (inner_M_fix' i j a b o) ++ drop (i + j)%nat o.
Proof.
  intros.
  assert(exists i', (Z.to_nat i' = i /\ i' = Z.of_nat i)%nat) by (exists (Z.of_nat i) ; split ; [apply Nat2Z.id|reflexivity]).
  destruct H as [i' [Hi' Hi'']].
  assert(exists j', (Z.to_nat j' = j /\ j' = Z.of_nat j)%nat) by (exists (Z.of_nat j) ; split ; [apply Nat2Z.id|reflexivity]).
  destruct H as [j' [Hj' Hj'']].
  repeat match goal with
    | _ => omega
    | _ => rewrite <- Hi'
    | _ => rewrite <- Hj'
    | _ => rewrite <- Z2Nat.inj_add
    | _ => rewrite <- inner_M_i_j_eq
    | _ => apply inner_M_fix_app_drop
   end.
Qed.

Lemma inner_M_fix_bounds : forall m1 m2 m3 n1 n2 n3 i j a b o p q,
  0 <= j ->
  0 <= i ->
  m1 <= a <= n1 ->
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m2 <= x <= n2) b ->
  Forall (fun x => m3 <= x <= n3) o ->
  length b = 16%nat ->
  length o = 31%nat ->
  p = m3 + min_prod m1 n1 m2 n2 ->
  q = n3 + max_prod m1 n1 m2 n2 ->
  Forall (fun x => p <= x <= q) (inner_M_fix i j a b o).
Proof.
  intros m1 m2 m3 n1 n2 n3 i j    a b o p q Hj Hi.
  gen a b o p q.
  apply (natlike_ind (fun j => ∀ (a : ℤ) (b o : list ℤ) (p q : ℤ),
m1 ≤ a ∧ a ≤ n1 → m1 ≤ 0 ∧ 0 ≤ n1 → m2 ≤ 0 ∧ 0 ≤ n2 → Forall (λ x : ℤ, m2 ≤ x ∧ x ≤ n2) b 
→ Forall (λ x : ℤ, m3 ≤ x ∧ x ≤ n3) o → length b = 16%nat → length o = 31%nat
            → p = m3 + min_prod m1 n1 m2 n2 → q = n3 + max_prod m1 n1 m2 n2
                → Forall (λ x : ℤ, p ≤ x ∧ x ≤ q) (inner_M_fix i j a b o)
)) ; try omega.
   - intros a b o p q Ha Hm1n1 Hm2n2 Hb Ho Hlb Hlo Hp Hq.
    rewrite inner_M_fix_0 ; try omega.
    assert(Hpmin:= min_prod_neg_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    assert(Hqmax:= max_prod_pos_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    eapply Forall_impl.
    eauto.
    intros x H; simpl in H.
    omega.
  - clear j Hj.
    intros j Hj iHj.
    intros a b o p q Ha Hm1n1 Hm2n2 Hb Ho Hlb Hlo Hp Hq.
    assert(Hpmin:= min_prod_neg_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    assert(Hqmax:= max_prod_pos_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    change (Z.succ j) with (j + 1).
    rewrite inner_M_fix_step ; try omega.
    rewrite inner_M_fix_app_drop ; try omega.
    unfold update_M_i_j.
    rewrite alter_app_r_alt.
    + apply Forall_app_2.
      apply Forall_take ; apply iHj ; go.
      assert((Z.to_nat (i + j) <= 31)%nat \/ (31 < Z.to_nat (i + j))%nat) by omega.
      destruct H.
      * rewrite take_length inner_M_fix_length ; try omega.
        rewrite min_l ; try omega.
        replace ((Z.to_nat (i + j) - Z.to_nat (i + j))%nat) with 0%nat by omega.
        apply le_lt_eq_dec in H.
        destruct H.
        (* get rid of second case: list is empty *)
        2: rewrite e  drop_ge ; go.
        remember (drop (Z.to_nat (i + j)) o) as t.
        destruct t.
        apply (f_equal (λ x, length x)) in Heqt.
        move: Heqt ; rewrite drop_length Hlo //=.
        (* first case where the list is empty is not possible *)
        assert(Hzw: Forall (λ x : ℤ, m3 ≤ x ∧ x ≤ n3) (z::t)).
          rewrite Heqt.
          apply Forall_drop.
          apply Ho.
        simpl.
        apply Forall_cons in Hzw ; destruct Hzw.
        apply Forall_cons_2.
        2: eapply Forall_impl ; eauto ; intros; simpl in *; omega.
        unfold local_update_M.
        assert(m2 <= from_option id 0 (b !! Z.to_nat j) <= n2).
          rewrite <- nth_lookup.
          apply Forall_nth_d ; eauto.
        assert( min_prod m1 n1 m2 n2 <= a * from_option id 0 (b !! Z.to_nat j) <= max_prod m1 n1 m2 n2).
          apply Mult_interval_correct_min_max_le ; omega.
        omega.
      * rewrite drop_ge.
        2: rewrite Hlo ; omega.
        rewrite take_ge.
        2: rewrite inner_M_fix_length ; [rewrite Hlo|] ; omega.
        replace ((alter (local_update_M (Z.to_nat j) a b)
     (Z.to_nat (i + j) - length (inner_M_fix i j a b o))%nat [])) with ([]:list Z) by (apply length_zero_iff_nil ; go).
         go.
    + rewrite take_length.
      apply Min.le_min_l.
Qed.

Close Scope Z.
