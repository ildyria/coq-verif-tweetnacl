Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.

Require Import Tweetnacl.Op.ScalarMult.
Require Import Tweetnacl.Op.A.
Require Import Tweetnacl.Op.M.
Require Import Prelude.prelude.prelude.
Require Import Recdef.

Local Open Scope Z.

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

Definition update_M2_i (i:nat) o := list_alter (local_update_M2 o (i + 16)) i o.

Function M2_fix (i : Z) (o : list Z) {measure Z.to_nat i} : list Z :=
  if (i <=? 0) then o else M2_fix (i - 1) (update_M2_i (Z.to_nat (i - 1)) o).
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Qed.

Fixpoint M2_fix' (i : nat) (o : list Z) := match i with
  | 0%nat => o
  | S p => M2_fix' p (update_M2_i p o)
end.

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

Close Scope Z.
