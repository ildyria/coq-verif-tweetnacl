Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.

Require Import Tweetnacl.Op.ScalarMult.
Require Import Tweetnacl.Op.A.
Require Import Tweetnacl.Op.M.
Require Import Prelude.prelude.prelude.
Require Import Recdef.

Local Open Scope Z.
(* convert_length_to_Zlength *)

Definition local_update_M (j:nat) (a:Z) (b : list Z) (x:Z) := x + a * ( from_option id 0 (b !! j)).

(* Definition update_M_i_j (i j a:Z) b o := list_alter (local_update_M (Z.to_nat j) a b) (Z.to_nat (i + j)) o. *)
Definition update_M_i_j (i j a:Z) b o := alter (local_update_M (Z.to_nat j) a b) (Z.to_nat (i + j)) o.
Definition update_M_i_j' (i j:nat) (a:Z) b o := list_alter (local_update_M j a b) (i + j)%nat o.

Lemma update_M_i_j_eq : forall (i j a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
    update_M_i_j i j a b o = update_M_i_j' (Z.to_nat i) (Z.to_nat j) a b o.
Proof.
  intros.
  unfold update_M_i_j.
  unfold update_M_i_j'.
  unfold alter.
  f_equal.
  rewrite Z2Nat.inj_add by omega.
  reflexivity.
Qed.

Lemma update_M_i_j_comm_j: forall (i j k a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
  0 <= k ->
  j <> k -> 
    update_M_i_j i j a b (update_M_i_j i k a b o) = update_M_i_j i k a b (update_M_i_j i j a b o).
Proof.
repeat match goal with
  | _ => omega
  | _ => progress intro
  | _ => progress unfold update_M_i_j
  | _ => apply list_alter_commute ; intro
  | [ H : Z.to_nat ( _ ) = Z.to_nat ( _ ) |- _ ] => apply Z2Nat.inj_iff in H ; omega
end.
Qed.

Function inner_M_fix (i j a:Z) (b o : list Z) {measure Z.to_nat j} : list Z :=
  if (j <=? 0) then o else inner_M_fix i (j - 1) a b (update_M_i_j i (j - 1) a b o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Fixpoint inner_M_fix' (i j : nat) (a:Z) (b o : list Z) := match j with
  | 0%nat => o
  | S p => inner_M_fix' i p a b (update_M_i_j' i p a b o)
end.

Lemma inner_M_i_j_eq : forall (i j a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
    inner_M_fix i j a b o = inner_M_fix' (Z.to_nat i) (Z.to_nat j) a b o.
Proof.
  intros i j a b o Hi Hj.
  gen b o.
  apply (natlike_ind (fun j => ∀ b o : list ℤ, inner_M_fix i j a b o = inner_M_fix' (Z.to_nat i) (Z.to_nat j) a b o)) ; try omega.
  intros ; rewrite inner_M_fix_equation ; auto.
  clear Hj j.
  intros j Hj iHj b o.
  change (Z.succ j) with (j + 1).
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)).
  rewrite inner_M_fix_equation.
  simpl.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (j + 1 - 1) with j.
  rewrite iHj.
  rewrite update_M_i_j_eq by omega.
  reflexivity.
  omega.
  rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
Qed.

Function inner_M_fix'' (i j a:Z) (b o : list Z) {measure Z.to_nat j} : list Z :=
  if (j <=? 0) then o else update_M_i_j i (j - 1) a b (inner_M_fix'' i (j - 1) a b o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Lemma inner_M_fix''_com: forall (i j k a:Z) (b o: list Z),
  0 <= i ->
  0 <= j ->
  j < k ->
    update_M_i_j i k a b (inner_M_fix'' i j a b o) = inner_M_fix'' i j a b (update_M_i_j i k a b o).
Proof.
  intros i j k a b o Hi Hj Hk.
  gen k b o.
  apply (natlike_ind (fun j => ∀ k : ℤ, j < k -> ∀ b o : list ℤ, update_M_i_j i k a b (inner_M_fix'' i j a b o) =
      inner_M_fix'' i j a b (update_M_i_j i k a b o))) ; try omega.
  - intros ; rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation ; auto.
  - clear Hj j ; intros j Hj iHj k Hk b o ; sort.
    change (Z.succ j) with (j + 1) in *.
    rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation.
    flatten.
    replace (j + 1 - 1) with (j) by omega.
    rewrite <- iHj by omega.
    rewrite update_M_i_j_comm_j by omega.
    reflexivity.
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
  - clear Hj j ; intros j Hj iHj b o ; sort.
    change (Z.succ j) with (j + 1).
    rewrite inner_M_fix_equation ; rewrite inner_M_fix''_equation.
    flatten.
    apply Z.leb_gt in Eq.
    replace (j + 1 - 1) with (j) by omega.
    rewrite iHj.
    rewrite inner_M_fix''_equation ; symmetry ; rewrite inner_M_fix''_equation.
    flatten.
    apply Z.leb_gt in Eq0.
    rewrite <- inner_M_fix''_com by omega.
    rewrite update_M_i_j_comm_j by omega.
    reflexivity.
Qed.

Lemma inner_M_fix_0 : forall i a b o, 0 <= i -> inner_M_fix i 0 a b o = o.
Proof.
intros ; rewrite inner_M_fix_equation ; flatten ; compute in Eq ; tryfalse.
Qed.

Lemma inner_M_fix_step j : 0 <= j -> forall i a b o, 0 <= i -> inner_M_fix i (j + 1) a b o = update_M_i_j i j a b (inner_M_fix i j a b o).
Proof.
  intros.
  rewrite inner_M_i_j_eq'' by omega.
  rewrite inner_M_fix''_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (j + 1 - 1) with (j) by omega.
  f_equal.
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
eapply (natlike_ind (fun j => ∀ i : ℤ,
0 ≤ i
→ ∀ (a : ℤ) (b o : list ℤ),
  i ≤ length o → inner_M_fix i j a b o = take (Z.to_nat i) o ++ drop (Z.to_nat i) (inner_M_fix i j a b o))) ; try omega.
intros; rewrite inner_M_fix_0 by omega; rewrite take_drop; reflexivity.
clear j Hj. intros j Hj iHj i Hi a b o Ho.
change (Z.succ j) with (j + 1).
rewrite inner_M_i_j_eq'' by omega.
rewrite inner_M_fix''_equation.
flatten.
rewrite take_drop; reflexivity.
replace (j + 1 - 1) with j by omega.
rewrite <- inner_M_i_j_eq'' by omega.
rewrite iHj by omega.
unfold update_M_i_j.
rewrite alter_app_r_alt.
f_equal.
2: rewrite take_length.
2: rewrite Z2Nat.inj_add by omega.
2: apply (NPeano.Nat.le_trans _ (Z.to_nat i)).
2: apply Min.le_min_l.
2: omega.
rewrite drop_app_ge.
2: rewrite take_length.
2: apply Min.le_min_l.
replace ((Z.to_nat i - length (take (Z.to_nat i) o)))%nat with 0%nat.
rewrite drop_0.
reflexivity.
rewrite take_length.
rewrite min_l ; go.
apply (NPeano.Nat.le_trans _ (Z.to_nat (length o))).
apply Z2Nat.inj_le ; go.
apply NPeano.Nat.eq_le_incl.
clear j Hj iHj i Hi b Ho Eq.
induction o ; go.
simpl.
rewrite Zpos_P_of_succ_nat.
rewrite Z2Nat.inj_succ ; go.
Qed.

Lemma inner_M_fix_app : forall i j a b o o', 0 <= j -> 0 <= i -> i + j <= length o -> inner_M_fix i j a b (o ++ o') = (inner_M_fix i j a b o) ++ o'.
Proof.
intros i j a b o o'; gen i j a b o'; induction o as [ | h o iHo] using rev_ind.
- intros. simpl in *.
replace i with 0 by omega.
replace j with 0 by omega.
subst ; repeat rewrite inner_M_fix_0 by omega ; auto.
- intros i j a b o' Hj Hi. gen i a b o'.
  apply (natlike_ind (fun j => ∀ i : ℤ,
0 ≤ i
→ ∀ (a : ℤ) (b o' : list ℤ),
  i + j <= length (o ++ [h]) → inner_M_fix i j a b ((o ++ [h]) ++ o') = inner_M_fix i j a b (o ++ [h]) ++ o')) ; try omega.
  intros.
  repeat rewrite inner_M_fix_0 by omega ; reflexivity.
  clear j Hj; intros j Hj iHj i Hi a b o' Hijo.
  change (Z.succ j) with (j + 1).
  repeat rewrite inner_M_i_j_eq'' by omega.
  rewrite inner_M_fix''_equation.
  symmetry.
  rewrite inner_M_fix''_equation.
  flatten.
  apply Z.leb_gt in Eq.
  replace (j + 1 - 1) with j by omega.
  repeat rewrite <- inner_M_i_j_eq'' by omega.
  change (Z.succ j) with (j + 1) in *.
  rewrite app_length in Hijo.
  simpl in Hijo.
  replace (i + (j + 1)) with ((i + j) + 1) in Hijo by omega.
  replace (ℤ.ℕ (length o + 1)%nat) with (length o + 1) in Hijo by (rewrite Nat2Z.inj_add ; simpl ; omega).
  assert(Hijo': i + j <= length o) by omega.
  clear Hijo.
  unfold update_M_i_j.
  rewrite <- alter_app_l.
  f_equal.
  replace ((o ++ [h]) ++ o') with (o ++ h::o').
  2: rewrite cons_middle; rewrite app_assoc_reverse ; reflexivity.
  rewrite iHo by omega.
  rewrite iHo by omega.
  rewrite app_assoc_reverse.
  rewrite cons_middle.
  reflexivity.
  rewrite inner_M_fix_length by omega.
  rewrite app_length. simpl.
  rewrite <- Nat2Z.id.
  apply Z2Nat.inj_lt.
  omega.
  omega.
  replace (ℤ.ℕ (length o + 1)%nat) with (length o + 1) by (rewrite Nat2Z.inj_add ; simpl ; omega).
  omega.
Qed.

Lemma inner_M_fix_take : forall i j a b o, 0 <= j -> 0 <= i -> i + j <= length o -> (inner_M_fix i j a b (take (Z.to_nat (i + j))  o)) = take (Z.to_nat (i + j)) (inner_M_fix i j a b o).
Proof.
intros.
symmetry.
rewrite <- (take_drop (Z.to_nat (i + j)) o).
rewrite inner_M_fix_app.
rewrite (take_drop (Z.to_nat (i + j)) o).
2: omega.
2: omega.
2: rewrite take_length.
rewrite take_app_ge.
2: rewrite inner_M_fix_length by omega.
2: rewrite take_length.
3: rewrite Nat2Z.inj_min.
3: rewrite Z.min_l.
3: rewrite Z2Nat.id ; omega.
3: rewrite Z2Nat.id ; omega.
2: apply Min.le_min_l.
rewrite inner_M_fix_length by omega.
rewrite take_length.
rewrite min_l.
replace ((Z.to_nat (i + j) - Z.to_nat (i + j))%nat) with 0%nat by omega.
replace (take 0 (drop (Z.to_nat (i + j)) o)) with (nil:list Z).
rewrite app_nil_r ; auto.
reflexivity.
apply Z2Nat.inj_le in H1.
rewrite <- Nat2Z.id.
omega.
omega.
omega.
Qed.



Lemma inner_M_fix_app_drop : forall i j a b o, 0 <= j -> 0 <= i -> i + j <= length o -> inner_M_fix i j a b o = take (Z.to_nat (i + j)) (inner_M_fix i j a b o) ++ drop (Z.to_nat (i + j)) o.
Proof.
intros i j a b o Hj Hi Hij.
rewrite <- (take_drop (Z.to_nat (i + j)) o) at 1.
rewrite inner_M_fix_app.
2: omega.
2: omega.
2: rewrite take_length.
2: rewrite min_l.
2: rewrite Z2Nat.id ; omega.
2: rewrite Z2Nat.inj_le in Hij by omega ; rewrite (Nat2Z.id (length o)) in Hij ; omega.
rewrite inner_M_fix_take by omega.
reflexivity.
Qed.

Lemma inner_M_fix_bounds : forall m1 m2 m3 n1 n2 n3 i j a b o p q,
  0 <= j ->
  0 <= i ->
  i + j <= 31 ->
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
i + j ≤ 31 -> m1 ≤ a ∧ a ≤ n1
→ m1 ≤ 0 ∧ 0 ≤ n1
  → m2 ≤ 0 ∧ 0 ≤ n2
    → Forall (λ x : ℤ, m2 ≤ x ∧ x ≤ n2) b
      → Forall (λ x : ℤ, m3 ≤ x ∧ x ≤ n3) o
        → length b = 16%nat
          → length o = 31%nat
            → p = m3 + min_prod m1 n1 m2 n2
              → q = n3 + max_prod m1 n1 m2 n2
                → Forall (λ x : ℤ, p ≤ x ∧ x ≤ q) (inner_M_fix i j a b o)
)) ; try omega.
  - intros a b o p q Hij Ha Hm1n1 Hm2n2 Hb Ho Hlb Hlo Hp Hq.
    rewrite inner_M_fix_0 by omega.
    assert(Hpmin:= min_prod_neg_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    assert(Hqmax:= max_prod_pos_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    eapply Forall_impl.
    eauto.
    intros x H; simpl in H.
    omega.
  - clear j Hj.
    intros j Hj iHj.
    intros a b o p q Hij Ha Hm1n1 Hm2n2 Hb Ho Hlb Hlo Hp Hq.
    assert(Hpmin:= min_prod_neg_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    assert(Hqmax:= max_prod_pos_le m1 n1 m2 n2 Hm1n1 Hm2n2).
    change (Z.succ j) with (j + 1).
    rewrite inner_M_fix_step by omega.
    rewrite inner_M_fix_app_drop.
    2: omega.
    2: omega.
    unfold update_M_i_j.
    rewrite alter_app_r_alt.
    + apply Forall_app_2.
      apply Forall_take ; apply iHj ; auto.
      omega.
        assert(Hij' : (Z.to_nat (i + j) <= 31)%nat).
        rewrite <- Nat2Z.id ; apply Z2Nat.inj_le ; [ | | change (ℤ.ℕ  31%nat) with 31] ; omega.
        rewrite take_length.
        rewrite inner_M_fix_length by omega.
        rewrite min_l by omega.
        replace ((Z.to_nat (i + j) - Z.to_nat (i + j))%nat) with 0%nat by omega.
        apply le_lt_eq_dec in Hij'.
        destruct Hij'.
        (* get rid of second case: list is empty *)
        2: rewrite e ; rewrite drop_ge ; go.
        remember (drop (Z.to_nat (i + j)) o) as t.
        destruct t.
        (* first case where the list is empty is not possible *)
          assert(length (drop (Z.to_nat (i + j)) o) > 0%nat).
            rewrite drop_length ; rewrite Hlo ; rewrite <- Nat2Z.inj_gt ; omega.
          rewrite <- Heqt in H.
          inversion H.
        assert(Hzw: Forall (λ x : ℤ, m3 ≤ x ∧ x ≤ n3) (z::t)).
          rewrite Heqt.
          apply Forall_drop.
          apply Ho.
        simpl.
        inversion Hzw.
        subst x l0.
        apply Forall_cons_2.
        2: eapply Forall_impl ; eauto ; intros; simpl in *; omega.
        unfold local_update_M.
        assert(m2 <= from_option id 0 (b !! Z.to_nat j) <= n2).
          rewrite <- nth_lookup.
          apply Forall_nth_d ; eauto.
        assert( min_prod m1 n1 m2 n2 <= a * from_option id 0 (b !! Z.to_nat j) <= max_prod m1 n1 m2 n2).
          apply Mult_interval_correct_min_max_le ; omega.
        omega.
    + rewrite take_length.
      apply Min.le_min_l.
    + rewrite Hlo.
      change (ℤ.ℕ  31%nat) with 31.
      omega.
Qed.

Function outer_M_fix (i j : Z) (a b o : list Z)  {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then o else outer_M_fix (i - 1) 16 a b (inner_M_fix (i - 1) j (from_option id 0 (a !! (Z.to_nat (i - 1)))) b o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Fixpoint outer_M_fix' (i j : nat) (a b o : list Z) := match i with
  | 0%nat => o
  | S p => outer_M_fix' p 16 a b (inner_M_fix' p j (from_option id 0 (a !! p)) b o)
end.

Lemma outer_M_i_j_eq : forall (i j:Z) (a b o: list Z),
  0 <= i ->
  0 <= j ->
    outer_M_fix i j a b o = outer_M_fix' (Z.to_nat i) (Z.to_nat j) a b o.
Proof.
  intros i j a b o Hi Hj.
  gen j a b o.
  gen i.
  apply (natlike_ind (fun i => ∀ j : ℤ, 0 ≤ j → ∀ a b o : list ℤ, outer_M_fix i j a b o = outer_M_fix' (Z.to_nat i) (Z.to_nat j) a b o)).
  intros ; rewrite outer_M_fix_equation ; auto.
  - intros i Hi IHi j Hj a b o.
    sort. (* sort the hypothesises *)
  change (Z.succ i) with (i + 1).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  rewrite outer_M_fix_equation.
  simpl.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (i + 1 - 1) with i by omega.
  rewrite IHi by omega.
  rewrite inner_M_i_j_eq by omega.
  replace (Z.to_nat 16) with 16%nat by reflexivity.
  reflexivity.
  rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
Qed.

Lemma outer_M_fix_0 : forall j a b o, outer_M_fix 0 j a b o = o.
Proof.
intros ; rewrite outer_M_fix_equation ; flatten ; compute in Eq ; tryfalse.
Qed.

Lemma outer_M_fix_length : forall i j a b o, 0 <= i -> 0 <= j -> length (outer_M_fix i j a b o) = length o.
Proof.
  intros i j a b o Hi; gen j a b o .
  apply (natlike_ind (fun i => ∀ (j : ℤ) (a b o : list ℤ), 0 <= j -> length (outer_M_fix i j a b o) = length o)) ; try omega.
  intros ; rewrite outer_M_fix_equation ; go.
  clear i Hi; intros i Hi iHi j a b o Hj.
  change (Z.succ i) with (i + 1).
  rewrite outer_M_fix_equation.
  destruct (i + 1 <=? 0) ; auto.
  replace (i + 1 - 1) with (i) by omega.
  rewrite iHi by omega.
  rewrite inner_M_fix_length ; go.
Qed.

Lemma outer_M_fix_Zlength : forall i j a b o, 0 <= i -> 0 <= j -> Zlength (outer_M_fix i j a b o) = Zlength o.
Proof. convert_length_to_Zlength outer_M_fix_length. Qed.

(* Lemma outer_M_fix_step : forall (i j : Z) (a b o : list Z),
  0 <= i ->
  0 <= j ->
    outer_M_fix (i + 1) j a b o = inner_M_fix i j (from_option id 0 (a !! (Z.to_nat i))) b (outer_M_fix i 16 a b o).
Proof.
  intros i j a b o Hi Hj.
  rewrite outer_M_fix_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (i + 1 - 1) with i by omega. *)
  

Definition M1_fix a b := outer_M_fix 16 16 a b [
  0;0;0;0;0;0;0;0;0;0;
  0;0;0;0;0;0;0;0;0;0;
  0;0;0;0;0;0;0;0;0;0;
  0].

Theorem M1_fix_eq_M1 : forall (a b o:list Z),
  (length a = 16)%nat ->
  (length b = 16)%nat ->
    M1_fix a b = mult_1 a b.
Proof.
  intros.
  unfold M1_fix.
  repeat (destruct a ; tryfalse).
  repeat (destruct b ; tryfalse).
  rewrite outer_M_i_j_eq by omega.
  change (Z.to_nat 16) with 16%nat.
  simpl.
  unfold update_M_i_j' ; simpl.
  unfold local_update_M.
  repeat rewrite <- nth_lookup.
  unfold nth.
  repeat (f_equal ; try ring).
Qed.

(*-------------------------------------------------------------------------------------*)

Definition local_update_M2 (y:list Z) (j:nat) (x:Z) := x + 38 * (from_option id 0 (y !! j)).

Definition update_M2_i (i:nat) o := alter (local_update_M2 o (i + 16)) i o.

Lemma update_M2_id : forall k o,
  (16 <= k)%nat ->
  (length o <= 31)%nat  ->
    update_M2_i k o = o.
Proof.
  intros.
  unfold update_M2_i.
  simpl.
  unfold local_update_M2.
  rewrite lookup_ge_None_2 by omega.
  simpl.
  apply list_alter_id ; auto.
  intros ; omega.
Qed.

Lemma update_M2_i_com: forall (i k: nat) (o: list Z),
  0 <= i ->
  0 <= k ->
  i < k -> 
  i + 16 <> k ->
    update_M2_i i (update_M2_i k o) = update_M2_i k (update_M2_i i o).
Proof.
  intros.
  unfold update_M2_i.
  remember (local_update_M2 (alter (local_update_M2 o (k + 16)) k o) (i + 16)) as f.
  remember (local_update_M2 o (k + 16)) as g.
  remember (local_update_M2 (alter (local_update_M2 o (i + 16)) i o) (k + 16)) as m.
  remember (local_update_M2 o (i + 16)) as n.
  unfold local_update_M2 in *.
  rewrite list_lookup_alter_ne in Heqf by omega.
  rewrite list_lookup_alter_ne in Heqm by omega.
  assert(g = m) by go.
  assert(f = n) by go.
  rewrite <- H3.
  rewrite <- H4.
  rewrite list_alter_commute ; go.
Qed.

Function M2_fix (i : Z) (o : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then o else M2_fix (i - 1) (update_M2_i (Z.to_nat (i - 1)) o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Fixpoint M2_fix' (i : nat) (o : list Z) := match i with
  | 0%nat => o
  | S p => M2_fix' p (update_M2_i p o)
end.

Function M2_fix'' (i : Z) (o : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then o else update_M2_i (Z.to_nat (i - 1)) (M2_fix'' (i - 1) o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Lemma M2_fix''_length : forall k l, 0 <= k -> length (M2_fix'' k l) = length l.
Proof.
  intros k l Hk; gen l.
  apply (natlike_ind (fun k => ∀ l : list ℤ, length (M2_fix'' k l) = length l)) ; try omega.
  intros ; rewrite M2_fix''_equation ; go.
  clear k Hk; intros i Hi iHi l.
  change (Z.succ i) with (i + 1).
  rewrite M2_fix''_equation.
  destruct (i + 1 <=? 0) ; auto.
  replace (i + 1 - 1) with (i) by omega.
  unfold update_M2_i.
  rewrite alter_length.
  apply iHi.
Qed.

Lemma M2_fix''_com : forall (i k : Z) (o : list Z), 
  (length o <= 31)%nat ->
  0 <= i ->
  i <= k ->
  k <= 16 -> (*let us hope this will be enough ! *)
    update_M2_i (Z.to_nat k) (M2_fix'' i o) = M2_fix'' i (update_M2_i (Z.to_nat k) o).
Proof.
  intros i k o Ho Hi.
  gen k o.
  apply (natlike_ind (fun i => (∀ (k : ℤ) (o : list ℤ),
(length o ≤ 31)%nat
→ i ≤ k
→ k ≤ 16
    → update_M2_i (Z.to_nat k) (M2_fix'' i o) = M2_fix'' i (update_M2_i (Z.to_nat k) o)))) ; try omega.
  - intros ; rewrite M2_fix''_equation ; symmetry ; rewrite M2_fix''_equation ; auto.
  - clear Hi i ; intros i Hi iHi k o Ho Hik Hkk ; sort.
    change (Z.succ i) with (i + 1) in *.
    rewrite M2_fix''_equation ; symmetry ; rewrite M2_fix''_equation.
    flatten.
    replace (i + 1 - 1) with (i) by omega.
    rewrite <- iHi by omega.
    apply Z_le_lt_eq_dec in Hkk.
    destruct Hkk.
    rewrite update_M2_i_com ; repeat rewrite Z2Nat.id by omega ; try omega.
    reflexivity.
    subst k.
    change (Z.to_nat 16) with 16%nat.
    repeat rewrite (update_M2_id 16); 
    unfold update_M2_i ; try rewrite alter_length ; try rewrite M2_fix''_length; try omega.
    reflexivity.
Qed.

Lemma update_M2_rec': forall (u:Z) (i:nat) (l:list Z),
  (update_M2_i (S i) (u::l)) = u::update_M2_i i l.
Proof.
  intros.
  unfold update_M2_i.
  unfold list_alter.
  reflexivity.
Qed.

Lemma update_M2_0: forall (x:Z) (l:list Z),
  (update_M2_i 0 (x::l)) =  x + 38 * (from_option id 0 ((x::l) !! 16%nat)) :: l.
Proof.
  intros.
  unfold update_M2_i.
  unfold list_alter.
  unfold local_update_M2.
  reflexivity.
Qed.

Lemma M2_fix_eq: forall (i: Z) (o: list Z),
  0 <= i ->
    M2_fix i o = M2_fix' (Z.to_nat i) o.
Proof.
  intros.
  gen i o.
  apply (natlike_ind (fun i => ∀ o : list ℤ, M2_fix i o = M2_fix' (Z.to_nat i) o)).
  intros ; rewrite M2_fix_equation ; auto.
  intros i Hi iHi o.
  change (Z.succ i) with (i + 1).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  rewrite M2_fix_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (i + 1 - 1) with i by omega.
  rewrite iHi; go.
  rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
Qed.

Lemma M2_fix_eq'': forall (i: Z) (o: list Z),
  0 <= i-> 
  (length o <= 31)%nat ->
  i <= 16 ->
    M2_fix i o = M2_fix'' i o.
Proof.
  intros i o Hi. gen o.
  eapply (natlike_ind (fun i => ∀ o : list ℤ, (length o ≤ 31)%nat → i ≤ 16 → M2_fix i o = M2_fix'' i o)) ; try omega.
  - intros ; rewrite M2_fix_equation ; rewrite M2_fix''_equation ;  auto.
  - clear i Hi; intros i Hi iHi o Ho Hii.
    change (Z.succ i) with (i + 1) in *.
    rewrite M2_fix_equation.
    rewrite M2_fix''_equation.
    flatten.
    replace (i + 1 - 1) with i by omega.
    rewrite iHi ; try omega.
    rewrite M2_fix''_equation.
    symmetry; rewrite M2_fix''_equation.
    flatten.
    apply Z.leb_gt in Eq ; apply Z.leb_gt in Eq0.
    rewrite <- M2_fix''_com by omega.
    rewrite <- update_M2_i_com ; repeat rewrite Z2Nat.id ; try omega.
    reflexivity.
    unfold update_M2_i.
    rewrite alter_length.
    omega.
Qed.

Lemma M2_fix_0 : forall (o: list Z), (M2_fix 0 o) = o.
Proof.
  intro o.
  rewrite M2_fix_equation.
  flatten.
  compute in Eq ; tryfalse.
Qed.

Lemma M2_fix_eq_step : forall (i: Z) (o: list Z),
  (length o <= 31)%nat ->
  0 <= i->
  i <= 16 ->
    update_M2_i (Z.to_nat (i + 1)) (M2_fix i o) = M2_fix i (update_M2_i (Z.to_nat (i + 1)) o).
Proof.
  intros.
  rewrite M2_fix_eq'' by omega.
  rewrite M2_fix_eq'' ; try (unfold update_M2_i ; rewrite alter_length); try omega.
  apply Z_le_lt_eq_dec in H1.
  destruct H1.
  rewrite M2_fix''_com; try omega.
  reflexivity.
  subst i.
  change (Z.to_nat (16 + 1)) with 17%nat.
  repeat rewrite (update_M2_id 17) ; go.
  rewrite M2_fix''_length ; omega.
Qed.

Lemma M2_fix_step : forall (i: Z) (o: list Z),
  (length o <= 31)%nat ->
  0 <= i->
  i <= 16 ->
    update_M2_i (Z.to_nat (i)) (M2_fix i o) = M2_fix (i + 1) o.
Proof.
  intros.
  symmetry.
  rewrite M2_fix_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  replace (i + 1 - 1) with i by omega.
  rewrite M2_fix_eq'' ; try omega.
  rewrite M2_fix_eq'' ; try (unfold update_M2_i ; rewrite alter_length); try omega.
  rewrite M2_fix''_com; try omega.
  reflexivity.
  unfold update_M2_i.
  rewrite alter_length.
  omega.
Qed.

Lemma M2_fix_stepZ : forall (i: Z) (o: list Z),
  Zlength o <= 31 ->
  0 <= i->
  i <= 16 ->
    update_M2_i (Z.to_nat (i)) (M2_fix i o) = M2_fix (i + 1) o.
Proof. convert_length_to_Zlength M2_fix_step. Qed.


Lemma M2_fix_length : forall (i: Z) (o: list Z),
  0 <= i ->
    length (M2_fix i o) = length o.
Proof.
  intros i l Hi; gen l.
  apply (natlike_ind (fun i => ∀ l : list ℤ, length (M2_fix i l) = length l)) ; try omega.
  intros ; rewrite M2_fix_0 ; go.
  clear i Hi; intros i Hi iHi l.
  change (Z.succ i) with (i + 1).
  rewrite M2_fix_equation.
  destruct (i + 1 <=? 0) ; auto.
  replace (i + 1 - 1) with (i) by omega.
  rewrite iHi.
  unfold update_M2_i.
  rewrite alter_length.
  auto.
Qed.

Lemma M2_fix_Zlength : forall (i: Z) (o: list Z),
  0 <= i ->
    Zlength (M2_fix i o) = Zlength o.
Proof. convert_length_to_Zlength M2_fix_length. Qed.

Theorem M2_fix_eq_M2 : forall (a:list Z),
  (length a = 31)%nat ->
  M2_fix 15 a = mult_2 a.
Proof.
intros.
repeat (destruct a ; tryfalse).
unfold mult_2 ; simpl.

repeat match goal with
  | [ |- context[Z.to_nat ?b] ] => change (Z.to_nat b) with b%nat
  | _ => progress unfold update_M2_i ; simpl
  | _ => progress unfold local_update_M2 ; repeat rewrite <- nth_lookup ; unfold nth
  | _ => reflexivity
  | _ => rewrite M2_fix_equation ; simpl
end.

(* rewrite M2_fix_eq by omega.
change (Z.to_nat 15) with 15%nat.
repeat rewrite update_M2_rec.
repeat (rewrite update_M2_0 ; simpl).
reflexivity. *)
Qed.

Theorem M2_fix_eq_M2Z : forall (a:list Z),
  Zlength a = 31 ->
  M2_fix 15 a = mult_2 a.
Proof. convert_length_to_Zlength M2_fix_eq_M2. Qed.


Function M3_fix (i : Z) (from : list Z) (to : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then to else 
    match from, to with
      | [], _  => to
      | _ , [] => []
      | f::from, t::to => f :: M3_fix (i - 1) from to
    end.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Fixpoint M3_fix' (i : nat) (from : list Z) (to : list Z) := match i, from, to with
  | 0%nat, _, to => to
  | _, [], to => to
  | _, _, [] => []
  | S p, f::from, t::to => f :: M3_fix' p from to
end.

Lemma M3_fix_eq : forall (i:Z) (f t:list Z), 0 <= i ->  M3_fix i f t = M3_fix' (Z.to_nat i) f t.
Proof.
  intros i f t Hi.
  gen i f t.
  apply (natlike_ind (fun i => ∀ f t : list ℤ, M3_fix i f t = M3_fix' (Z.to_nat i) f t)).
  intros; rewrite M3_fix_equation ; auto.
  intros i Hi iHi from to.
  change (Z.succ i) with (i + 1).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  rewrite M3_fix_equation.
  flatten ; 
  try (apply Zle_bool_imp_le in Eq ; omega); (* silly case *)
  apply Z.leb_gt in Eq ; replace (i + 1 - 1) with i by omega ; go.
  rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
Qed.

Lemma M3_fix_0 : forall (f t:list Z),
    M3_fix 0 f t = t.
Proof.
  intros f t.
  rewrite M3_fix_equation.
  destruct (0 <=? 0) eqn:H ; [| compute in H]; go.
Qed.

Lemma M3_fix_step : forall (i:Z) (f t:list Z),
  0 <= i < 16 -> 
  length t = 16%nat -> 
  length f = 31%nat ->
    M3_fix (i + 1) f t = ((take (Z.to_nat i) (M3_fix i f t)) ++ [nth (Z.to_nat i) f 0]) ++ drop (Z.to_nat i + 1) (M3_fix i f t).
Proof.
intros.
repeat (destruct t; tryfalse).
do 16 (destruct f; tryfalse).
repeat rewrite M3_fix_eq ; try omega.
rewrite Z2Nat.inj_add ; try omega.
remember ((Z.to_nat i)%nat) as j.
replace (Z.to_nat 1) with 1%nat by reflexivity.
replace (j + 1)%nat with (S j)%nat by omega.
assert((j < 16)%nat).
rewrite Heqj.
change (16%nat) with (Z.to_nat 16).
apply Z2Nat.inj_lt ; omega.
simpl.
flatten ; simpl ; try reflexivity.
simpl in Heqj.
exfalso.
assert(forall n, 16 <= (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S n))))))))))))))))) by (induction 1 ; omega).
omega.
Qed.

Lemma M3_fix_stepZ : forall (i:Z) (f t:list Z),
  0 <= i < 16 -> 
  Zlength t = 16 -> 
  Zlength f = 31 ->
    M3_fix (i + 1) f t = ((take (Z.to_nat i) (M3_fix i f t)) ++ [nth (Z.to_nat i) f 0]) ++ drop (Z.to_nat i + 1) (M3_fix i f t).
Proof. convert_length_to_Zlength M3_fix_step. Qed.

Theorem M3_fix_eq_M3 : forall (from to:list Z)  ,
  (length from = 31)%nat ->
  (length to = 16)%nat ->
  M3_fix 16 from to = mult_3 from.
Proof.
  intros.
  repeat (destruct from ; tryfalse).
  repeat (destruct to ; tryfalse).
  rewrite M3_fix_eq by omega.
  change (Z.to_nat 16) with 16%nat.
  reflexivity.
Qed.

Theorem M3_fix_eq_M3Z : forall (from to:list Z)  ,
  Zlength from = 31 ->
  Zlength to = 16 ->
  M3_fix 16 from to = mult_3 from.
Proof. convert_length_to_Zlength M3_fix_eq_M3. Qed.

Lemma M3_fix_length: forall (i: Z) (f t: list Z),
  length t = length (M3_fix i f t).
Proof. intros ; gen i f ; induction t ; intros ; rewrite M3_fix_equation; flatten; go. Qed.

Lemma M3_fix_Zlength: forall (i: Z) (f t: list Z),
  Zlength t = Zlength (M3_fix i f t).
Proof. intros; repeat rewrite Zlength_correct; rewrite <- M3_fix_length ; reflexivity. Qed.

Close Scope Z.
