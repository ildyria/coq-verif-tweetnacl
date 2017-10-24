Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.

Require Import Tweetnacl.Op.Inner_M1.
Require Import Tweetnacl.Op.Outer_M1.
Require Import Tweetnacl.Op.M.
Require Import stdpp.prelude.
Require Import Recdef.

Local Open Scope Z.

Definition M1_fix a b := outer_M_fix 16 0 a b [
  0;0;0;0;0;0;0;0;0;0;
  0;0;0;0;0;0;0;0;0;0;
  0;0;0;0;0;0;0;0;0;0;
  0].

Theorem M1_fix_eq_M1 : forall (a b:list Z),
  (length a = 16)%nat ->
  (length b = 16)%nat ->
    M1_fix a b = mult_1 a b.
Proof.
  intros.
  unfold M1_fix.
  repeat (destruct a ; tryfalse).
  repeat (destruct b ; tryfalse).
  orewrite outer_M_i_j_eq.
  change (Z.to_nat 16) with 16%nat.
  simpl.
  unfold update_M_i_j' ; simpl.
  unfold local_update_M.
  repeat rewrite <- nth_lookup.
  unfold nth.
  repeat rewrite Z.add_0_r.
  reflexivity.
Qed.

Theorem M1_fix_eq_M1Z : forall (a b:list Z),
  Zlength a = 16 ->
  Zlength b = 16 ->
    M1_fix a b = mult_1 a b.
Proof. convert_length_to_Zlength M1_fix_eq_M1. Qed.

Lemma M1_fix_length : forall (a b: list Z),
  (length a = 16)%nat ->
  (length b = 16)%nat ->
    length (M1_fix a b) = 31%nat.
Proof. intros; unfold M1_fix; rewrite outer_M_fix_length ; go. Qed.

Lemma M1_fix_Zlength : forall (a b o: list Z),
  Zlength a = 16 ->
  Zlength b = 16 ->
    Zlength (M1_fix a b) = 31.
Proof. convert_length_to_Zlength M1_fix_length. Qed.


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
  orewrite (@lookup_ge_None_2 Z).
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
  move: Heqf ; orewrite (@list_lookup_alter_ne Z) => Heqf.
  move: Heqm ; orewrite (@list_lookup_alter_ne Z) => Heqm.
  assert(g = m) by go.
  assert(f = n) by go.
  rewrite <- H3.
  rewrite <- H4.
  rewrite list_alter_commute ; go.
Qed.

Function M2_fix (i : Z) (o : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then o else M2_fix (i - 1) (update_M2_i (Z.to_nat (i - 1)) o).
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Qed.

Fixpoint M2_fix' (i : nat) (o : list Z) := match i with
  | 0%nat => o
  | S p => M2_fix' p (update_M2_i p o)
end.

Function M2_fix'' (i : Z) (o : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then o else update_M2_i (Z.to_nat (i - 1)) (M2_fix'' (i - 1) o).
Proof. intros. apply Z2Nat.inj_lt ;  move: teq ; rewrite Z.leb_gt => teq; omega. Qed.

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
    rewrite update_M2_i_com ; repeat orewrite Z2Nat.id.
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
  2: rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite M2_fix_equation.
  flatten.
  apply Zle_bool_imp_le in Eq ; omega. (* silly case *)
  apply Z.leb_gt in Eq.
  replace (i + 1 - 1) with i by omega.
  rewrite iHi; go.
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
    2: unfold update_M2_i ; rewrite alter_length ; omega.
    rewrite M2_fix''_equation.
    symmetry; rewrite M2_fix''_equation.
    flatten.
    apply Z.leb_gt in Eq ; apply Z.leb_gt in Eq0.
    rewrite <- M2_fix''_com by omega.
    rewrite <- update_M2_i_com ; repeat rewrite Z2Nat.id ; try omega.
    reflexivity.
Qed.

Lemma M2_fix_0 : forall (o: list Z), (M2_fix 0 o) = o.
Proof. intro o ; rewrite M2_fix_equation ; flatten ; compute in Eq ; tryfalse. Qed.

Lemma M2_fix_eq_step : forall (i: Z) (o: list Z),
  (length o <= 31)%nat ->
  0 <= i->
  i <= 16 ->
    update_M2_i (Z.to_nat (i + 1)) (M2_fix i o) = M2_fix i (update_M2_i (Z.to_nat (i + 1)) o).
Proof.
  intros.
  orewrite M2_fix_eq''.
  rewrite M2_fix_eq'' ; try (unfold update_M2_i ; rewrite alter_length) ; try omega.
  apply Z_le_lt_eq_dec in H1.
  destruct H1.
  rewrite M2_fix''_com; try omega ; reflexivity.
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
  repeat (rewrite M2_fix_eq'' ; try (unfold update_M2_i ; rewrite alter_length); try omega).
  rewrite M2_fix''_com; try omega.
  reflexivity.
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
  - intros ; rewrite M2_fix_0 ; go.
  - clear i Hi; intros i Hi iHi l.
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

Qed.

Theorem M2_fix_eq_M2Z : forall (a:list Z),
  Zlength a = 31 ->
  M2_fix 15 a = mult_2 a.
Proof. convert_length_to_Zlength M2_fix_eq_M2. Qed.


Theorem M2_fix_drop : forall i (a: list Z),
  0 <= i < 16 -> 
  (length a = 31)%nat ->
  drop 16 (M2_fix i a) = drop 16 a.
Proof.
  intros i a Hi Hla.
  repeat (destruct a ; tryfalse).
  gen_i H i ; simpl M2_fix ; rewrite M2_fix_eq ; try omega; change_Z_to_nat ; simpl ; reflexivity.
Qed.

Theorem M2_fix_dropZ : forall i (a: list Z),
  0 <= i < 16 -> 
  Zlength a = 31 ->
  drop 16 (M2_fix i a) = drop 16 a.
Proof. convert_length_to_Zlength M2_fix_drop. Qed.

Lemma M2_fix_bounds : forall m1 n1 p q (a: list Z) i,
  0 <= i ->
  i < 16 ->
  (fun x => m1 <= x <= n1) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  (length a = 31)%nat ->
  p = m1 + 38 * m1 ->
  q = n1 + 38 * n1 ->
  Forall (fun x => p <= x <= q) (M2_fix i a).
Proof.
  intros m1 n1 p q a i Hi Hi' Hm1n1 Ha Hla Hp Hq.
  simpl in Hm1n1.
  assert(Hpm: p <= m1) by omega.
  assert(Hqn: n1 <= q) by omega.
  repeat (destruct a ; tryfalse).
  gen_i H i ; rewrite M2_fix_eq ; try omega; change_Z_to_nat ; simpl ; repeat match goal with 
  | [H : context[Forall] |- _ ] => apply Forall_cons in H ; destruct H
  end;
  repeat match goal with
  | [ |- update_M2_i (S _) _ ] => rewrite update_M2_rec' ; simpl
  | [ |- context[local_update_M2]] => unfold local_update_M2 ; simpl
  | [ |- update_M2_i 0 (_ :: _) ] => rewrite update_M2_0 ; simpl
  | [ |- Forall _ [] ] => go
  | [ |- _ ≤ _ ∧ _ ≤ _ ] => omega
  | [ |- Forall _ _ ] => apply Forall_cons_2
  end.
Qed.

Lemma M2_fix_Zbounds : forall m1 n1 p q (a: list Z) i,
  0 <= i ->
  i < 16 ->
  (fun x => m1 <= x <= n1) 0 ->
  Forall (fun x => m1 <= x <= n1) a ->
  Zlength a = 31 ->
  p = m1 + 38 * m1 ->
  q = n1 + 38 * n1 ->
  Forall (fun x => p <= x <= q) (M2_fix i a).
Proof. convert_length_to_Zlength M2_fix_bounds; eapply M2_fix_bounds ; go. Qed.




(*-------------------------------------------------------------------------------------*)



Function M3_fix (i : Z) (from : list Z) (to : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then to else 
    match from, to with
      | [], _  => to
      | _ , [] => []
      | f::from, t::to => f :: M3_fix (i - 1) from to
    end.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Qed.

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
  2: rewrite Z2Nat.inj_add ; try replace (Z.to_nat 1) with 1%nat by reflexivity ; omega.
  rewrite M3_fix_equation.
  flatten ; 
  try (apply Zle_bool_imp_le in Eq ; omega); (* silly case *)
  apply Z.leb_gt in Eq ; replace (i + 1 - 1) with i by omega ; go.
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
  orewrite M3_fix_eq.
  change (Z.to_nat 16) with 16%nat.
  reflexivity.
Qed.

Theorem M3_fix_eq_M3' : forall (from to:list Z)  ,
  (length from = 31)%nat ->
  (length to = 16)%nat ->
  M3_fix 16 from to = mult_3 from.
Proof.
  intros.
  repeat (destruct from ; tryfalse).
  repeat (destruct to ; tryfalse).
  orewrite M3_fix_eq.
  change (Z.to_nat 15) with 15%nat.
  simpl.
  unfold mult_3.
  simpl.
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
