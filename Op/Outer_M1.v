Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Op.Inner_M1.
Require Import stdpp.prelude.
Require Import Recdef.

Local Open Scope Z.

Function outer_M_fix (i j : Z) (a b o : list Z)  {measure Z.to_nat i} : list Z :=
  if (i <=? 0)
    then (inner_M_fix 0 j (from_option id 0 (a !! (Z.to_nat 0))) b o)
    else outer_M_fix (i - 1) 16 a b (inner_M_fix i j (from_option id 0 (a !! (Z.to_nat i))) b o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Fixpoint outer_M_fix' (i j : nat) (a b o : list Z) := match i with
  | 0%nat => (inner_M_fix' 0%nat j (from_option id 0 (a !! 0%nat)) b o)
  | S p => outer_M_fix' p 16 a b (inner_M_fix' (S p) j (from_option id 0 (a !! (S p))) b o)
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
  intros.
  rewrite outer_M_fix_equation.
  rewrite Zle_imp_le_bool by omega.
  rewrite inner_M_i_j_eq by omega.
  simpl.
  f_equal.
  - intros i Hi IHi j Hj a b o.
    sort. (* sort the hypothesises *)
  change (Z.succ i) with (i + 1).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  2:   rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite outer_M_fix_equation; simpl.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (i + 1 - 1) with i by omega.
  rewrite IHi by omega.
  rewrite inner_M_i_j_eq by omega.
  f_equal; f_equal ; [| f_equal;f_equal] ; rewrite <- Z2Nat.inj_succ ; go.
Qed.

Lemma outer_M_fix_0 : forall a b o, outer_M_fix 0 0 a b o = o.
Proof.
intros ; rewrite outer_M_fix_equation ; flatten ; compute in Eq ; tryfalse.
rewrite inner_M_fix_0 ; go.
Qed.

Lemma outer_M_fix_0' : forall a b o j , outer_M_fix 0 j a b o = inner_M_fix 0 j (from_option id 0 (a !! Z.to_nat 0)) b o.
Proof. intros ; rewrite outer_M_fix_equation ; flatten ; compute in Eq ; tryfalse. Qed.

Lemma outer_M_fix_length : forall i j a b o, 0 <= i -> 0 <= j -> length (outer_M_fix i j a b o) = length o.
Proof.
  intros i j a b o Hi; gen j a b o .
  apply (natlike_ind (fun i => ∀ (j : ℤ) (a b o : list ℤ), 0 <= j -> length (outer_M_fix i j a b o) = length o)) ; try omega.
  intros ; rewrite outer_M_fix_equation ; go.
  flatten.
  rewrite inner_M_fix_length ; go.
  tryfalse.
  clear i Hi; intros i Hi iHi j a b o Hj.
  change (Z.succ i) with (i + 1).
  rewrite outer_M_fix_equation.
  destruct (i + 1 <=? 0) ; auto.
  rewrite inner_M_fix_length ; go.
  replace (i + 1 - 1) with (i) by omega.
  rewrite iHi by omega.
  rewrite inner_M_fix_length ; go.
Qed.

Lemma outer_M_fix_Zlength : forall i j a b o, 0 <= i -> 0 <= j -> Zlength (outer_M_fix i j a b o) = Zlength o.
Proof. convert_length_to_Zlength outer_M_fix_length. Qed.

Lemma outer_M_fix_bounds : forall m1 m2 m3 n1 n2 n3 i j a b o p q,
  0 <= i ->
  0 <= j ->
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  Forall (fun x => m2 <= x <= n2) b ->
  Forall (fun x => m3 <= x <= n3) o ->
  length a = 16%nat ->
  length b = 16%nat ->
  length o = 31%nat ->
  p = m3 + (i + 1) * min_prod m1 n1 m2 n2 ->
  q = n3 + (i + 1) * max_prod m1 n1 m2 n2 ->
  Forall (fun x => p <= x <= q) (outer_M_fix i j a b o).
Proof.
  intros m1 m2 m3 n1 n2 n3 i j a b o p q Hi Hj Hm1n1 Hm2n2 Ha Hb Ho Hla Hlb Hlo Hp Hq.
  gen j a b o p q m3 n3.
   apply (natlike_ind (fun i => ∀ j : ℤ,
0 ≤ j
→ ∀ a : list ℤ,
  Forall (λ x : ℤ, m1 ≤ x ∧ x ≤ n1) a
  → length a = 16%nat
    → ∀ b : list ℤ,
      Forall (λ x : ℤ, m2 ≤ x ∧ x ≤ n2) b
      → length b = 16%nat
        → ∀ o : list ℤ,
          length o = 31%nat
          → ∀ p q m3 : ℤ,
            p = m3 + (i + 1) * min_prod m1 n1 m2 n2
            → ∀ n3 : ℤ,
              Forall (λ x : ℤ, m3 ≤ x ∧ x ≤ n3) o
              → q = n3 + (i + 1) * max_prod m1 n1 m2 n2
                → Forall (λ x : ℤ, p ≤ x ∧ x ≤ q) (outer_M_fix i j a b o))) ; try omega.
- intros j Hj a Ha Hla b Hb Hlb o Hlo p q m3 Hp n3 Ho Hq.
  rewrite outer_M_fix_0'.
  replace ((0 + 1) * min_prod m1 n1 m2 n2) with (min_prod m1 n1 m2 n2) in Hp by omega.
  replace ((0 + 1) * max_prod m1 n1 m2 n2) with (max_prod m1 n1 m2 n2) in Hq by omega.
  eapply inner_M_fix_bounds ; try omega.
  2: apply Hm1n1.
  2: apply Hm2n2.
  rewrite <- nth_lookup.
  apply Forall_nth_len.
  auto.
  rewrite Hla ; go.
  auto.
  eauto.
  eauto.
  eauto.
- clear i Hi ; intros i Hi iHi.
  intros j Hj a Ha Hla b Hb Hlb o Hlo p q m3 Hp n3 Ho Hq.
  rewrite outer_M_fix_equation.
  flatten.
    apply Zle_bool_imp_le in Eq ; rewrite <- Z.add_1_l in Eq ; omega.
  rewrite <- Z.add_1_r.
  replace (i + 1 - 1) with i by omega.
  subst p q.
  replace (m3 + (Z.succ i + 1) * min_prod m1 n1 m2 n2) with
   ((m3 + min_prod m1 n1 m2 n2) + (i + 1) * min_prod m1 n1 m2 n2) by ring.
  replace (n3 + (Z.succ i + 1) * max_prod m1 n1 m2 n2) with
   ((n3 + max_prod m1 n1 m2 n2) + (i + 1) * max_prod m1 n1 m2 n2) by ring.
   remember (m3 + min_prod m1 n1 m2 n2) as m3'.
   remember (n3 + max_prod m1 n1 m2 n2) as n3'.
  eapply iHi ; try omega ; try assumption.
  rewrite inner_M_fix_length ; auto.
  eauto.
  2: eauto.
  simpl in Hm1n1, Hm2n2.
  subst.
  eapply inner_M_fix_bounds ; try omega.
  2: eapply Hm1n1.
  2: eapply Hm2n2.
  2: assumption.
  2: eauto.
  2: eauto.
  2: eauto.
  rewrite <- nth_lookup.
  eapply Forall_nth_d ; go.
Qed.



Lemma outer_M_fix_Zbounds : forall m1 m2 m3 n1 n2 n3 i j a b o p q,
  0 <= i ->
  0 <= j ->
  (fun x => m1 <= x <= n1) 0 ->
  (fun x => m2 <= x <= n2) 0 ->
  Forall (fun x => m1 < x < n1) a ->
  Forall (fun x => m2 < x < n2) b ->
  Forall (fun x => m3 <= x <= n3) o ->
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength o = 31 ->
  p = m3 + (i + 1) * min_prod m1 n1 m2 n2 ->
  q = n3 + (i + 1) * max_prod m1 n1 m2 n2 ->
  Forall (fun x => p <= x <= q) (outer_M_fix i j a b o).
Proof.
intros.
rewrite Zlength_correct in H6, H7, H8.
eapply (outer_M_fix_bounds m1 m2 m3 n1 n2 n3) ; go.
eapply Forall_impl ; [eapply H3|]; intros ; go.
eapply Forall_impl ; [eapply H4|]; intros ; go.
Qed.

Close Scope Z.