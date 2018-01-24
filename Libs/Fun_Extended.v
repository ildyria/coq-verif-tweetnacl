(* Set Warnings "-notation-overridden".
Require Export Coq.ZArith.ZArith.
Require Import List.
Require Import Tweetnacl.Libs.Fun_Decidable.

Open Scope Z.

Section fun_rec.

Context {T:Type} (n:Z) (f : Z -> list T -> list T). (* (Hn : 0 <= n). *)
Variable P : T -> Prop.
Variable Q : T -> Prop.
Variable f_P_to_Q : forall n l d, P (nth (Z.to_nat n) l d) -> Q (nth (Z.to_nat n) (f n l) d).

Lemma sub_fn_rev_s_1 : forall (l:list T) (d:T),
  0 <= n ->
  (forall m, 0 < m -> P (nth (Z.to_nat m) l d)) ->
  Q (nth (Z.to_nat 0) l d) ->
  forall m, m < n -> Q (nth (Z.to_nat m) (sub_fn_rev_s 1 f n l) d).
Proof.
revert n.
induction n using Z.peano_ind.
intros.
rewrite sub_fn_rev_s_equation.
replace (0 <=? 1) with true.
2: reflexivity.
destruct m.
assumption.
assert(HP := Pos2Z.is_pos p) ; omega.
rewrite Z2Nat.inj_neg ; apply H1.
intros.
rewrite sub_fn_rev_s_equation.
destruct (Z.succ z <=? 1) eqn:?.
apply Zle_bool_imp_le in Heqb.
rewrite <- Z.add_1_r in Heqb.
assert( z <= 0).
omega.
rewrite <- Z.add_1_r in H2.

assert( m = 0).
Search Z.succ Z.add.
Search "<=?" true.
intros l d HP HQ.
Search Z "ind".
induction m.
intros. *)