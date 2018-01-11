Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import ssreflect.
Open Scope Z.

Definition step_pow_Z a c g := let c0 := c*c in if Zneq_bool a 1 && Zneq_bool a 3 then c0*g else c0.

Function pow_fn_rev_Z (a b:Z) (c g: Z) {measure Z.to_nat a} : (Z) :=
  if (a <=? 0)
    then c
    else
      let prev := pow_fn_rev_Z (a - 1) b c g in 
        step_pow_Z (b - 1 - a) prev g.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma pow_fn_rev_Z_n : forall a b c g,
  0 < a ->
  pow_fn_rev_Z a b c g = step_pow_Z (b - 1 - a) (pow_fn_rev_Z (a - 1) b c g) g.
Proof. intros. rewrite pow_fn_rev_Z_equation. flatten; apply Zle_bool_imp_le in Eq; omega. Qed.

Definition Inv25519_Z (x:Z) : Z := pow_fn_rev_Z 254 254 x x.

(*****************************************************************************************
 *   DEFINE SEMANTIC
 *)

Inductive expr_inv :=
  | R_inv : expr_inv
  | M_inv : expr_inv -> expr_inv -> expr_inv
  | S_inv : expr_inv -> expr_inv
  | P_inv : expr_inv -> positive -> expr_inv.

Inductive formula_inv := 
  | Eq_inv : expr_inv -> expr_inv -> formula_inv.

Fixpoint expr_inv_denote v env (m : expr_inv) : Z :=
  match m with
  | R_inv     => term_denote env v
  | M_inv x y => (expr_inv_denote v env x) * (expr_inv_denote v env y)
  | S_inv x => (expr_inv_denote v env x) * (expr_inv_denote v env x)
  | P_inv x p => Z.pow (expr_inv_denote v env x) (Z.pos p)
  end.

Definition formula_inv_denote v env (t : formula_inv) : Prop :=
  match t with
  | Eq_inv x y     => expr_inv_denote v env x = expr_inv_denote v env y
  end.

(*****************************************************************************************
 *   DECIDE EQUALITY
 *)

Fixpoint compute_pow_expr_inv (t : expr_inv) : Z := match t with
  | R_inv   => 1
  | M_inv x y => (compute_pow_expr_inv x) + (compute_pow_expr_inv y)
  | S_inv x => 2 * (compute_pow_expr_inv x)
  | P_inv x p => (Z.pos p) * (compute_pow_expr_inv x)
  end.

Lemma compute_pow_expr_inv_pos : forall l, 0 <= compute_pow_expr_inv l.
Proof. induction l ; go. Qed.

Lemma compute_pow_expr_M_inv_pos : forall l l', 0 <= compute_pow_expr_inv (M_inv l l').
Proof. intros ; simpl.
assert(H := compute_pow_expr_inv_pos l).
assert(H' := compute_pow_expr_inv_pos l') ; omega.
Qed.

Lemma compute_pow_expr_S_inv_pos : forall l, 0 <= compute_pow_expr_inv (S_inv l).
Proof. intros ; simpl.
assert(H := compute_pow_expr_inv_pos l) ; omega.
Qed.

Lemma compute_pow_expr_inv_denote: forall env v l,
  expr_inv_denote v env l = Z.pow (term_denote env v) (compute_pow_expr_inv l).
Proof.
  induction l.
  simpl ; ring.
  assert(Hl1:= compute_pow_expr_inv_pos l1).
  assert(Hl2:= compute_pow_expr_inv_pos l2).
  simpl; rewrite IHl1 IHl2 -Z.pow_add_r; go.
  assert(Hl1:= compute_pow_expr_inv_pos l).
  simpl; rewrite IHl -Z.pow_add_r ; go.
  f_equal ; omega.
  assert(Hl1:= compute_pow_expr_inv_pos l).
  assert(Hp:= Pos2Z.is_nonneg p).
  simpl; rewrite IHl -Z.pow_mul_r; go.
  by rewrite Z.mul_comm.
Qed.

Fixpoint decide_expr_inv_eq (l1 l2:expr_inv) :=
  Z.eqb (compute_pow_expr_inv l1) (compute_pow_expr_inv l2).

Lemma decide_expr_inv_eq_refl_impl : forall l1 l2, 
  Z.eqb (compute_pow_expr_inv l1) (compute_pow_expr_inv l2) = true ->
  (compute_pow_expr_inv l1) = (compute_pow_expr_inv l2).
Proof. move=> l1 l2; rewrite Z.eqb_eq //. Qed.

Lemma decide_expr_inv_eq_impl:
  forall v env l l', 
  decide_expr_inv_eq l l' = true ->
  expr_inv_denote v env l = expr_inv_denote v env l'.
Proof.
intros; rewrite ?compute_pow_expr_inv_denote; f_equal.
gen l'; induction l ; destruct l' ; auto => H;
apply decide_expr_inv_eq_refl_impl in H ; by rewrite H.
Qed.

Definition decide_formula_inv (f : formula_inv) : bool := match f with
  | Eq_inv x y => decide_expr_inv_eq x y
  end.

Lemma decide_formula_inv_impl : forall v env f, decide_formula_inv f = true -> formula_inv_denote v env f.
Proof. move=> v env [? ?]. by apply decide_expr_inv_eq_impl. Qed.

(* Weaponize our expression so we can translate functions *)


Definition step_inv a c g : expr_inv := 
  let c0 := (S_inv c) in if negb (Nat.eqb a 1) && negb (Nat.eqb a 3) then M_inv c0 g else c0.

Lemma step_inv_step_pow_eq : forall v env a c g,
  expr_inv_denote v env (step_inv (Z.to_nat a) c g) =  step_pow_Z a (expr_inv_denote v env c) (expr_inv_denote v env g).
Proof.
  intros.
  rewrite /step_inv /step_pow_Z.
  flatten.
  { reflexivity. }
  {
  exfalso.
  apply andb_true_iff in Eq.
  destruct Eq as [Eq2 Eq4].
  apply andb_false_iff in Eq0.
  apply negb_true_iff in Eq2.
  apply negb_true_iff in Eq4.
  apply beq_nat_false in Eq2.
  apply beq_nat_false in Eq4.
  destruct Eq0 as [Eq|Eq];
  rewrite /Zneq_bool in Eq ; flatten Eq;
  apply Z.compare_eq_iff in Eq0 ; go.
  }
  {
  exfalso.
  apply andb_true_iff in Eq0.
  destruct Eq0 as [Eq2 Eq4].
  assert(a < 0 \/ 0 <= a) by omega.
  destruct H.
    assert(Z.to_nat a = 0%nat) by (unfold Z.to_nat ; destruct a => //).
    rewrite H0 in Eq.
    by compute in Eq.
  apply andb_false_iff in Eq.
  destruct Eq as [Eq|Eq];
  apply negb_false_iff in Eq ; apply beq_nat_true in Eq;
  apply (f_equal Z.of_nat) in Eq;
  rewrite Z2Nat.id in Eq; try assumption;
  compute in Eq;
  subst a;
  by compute in Eq2,Eq4.
  }
  { reflexivity. }
Qed.

Close Scope Z.

Fixpoint pow_inv (a b : nat) (c g: expr_inv) : expr_inv := match a with
  | 0 => c
  | S n => let prev := pow_inv n b c g in 
              step_inv (b - 1 - a) prev g
  end.

Open Scope Z.

Lemma pow_inv_pow_fn_rev_eq : forall v env a b c g,
  expr_inv_denote v env (pow_inv (Z.to_nat a) (Z.to_nat b) c g) =  pow_fn_rev_Z a b (expr_inv_denote v env c) (expr_inv_denote v env g).
Proof.
  intros.
  destruct a; intros ; [ go | | go ].
  remember (Z.pos p) as a.
  assert(0 <= a) by (subst; apply Zle_0_pos).
  clears p.
  gen b c g.
  gen a.
  apply (natlike_ind (fun a => forall (b : ℤ) (c g : expr_inv),
    expr_inv_denote v env (pow_inv (Z.to_nat a) (Z.to_nat b) c g) =
    pow_fn_rev_Z a b (expr_inv_denote v env c) (expr_inv_denote v env g))) => //.
  intros a Ha IHa b c g.
  orewrite pow_fn_rev_Z_n.
  oreplace (Z.succ a - 1) a.
  replace ((Z.to_nat (Z.succ a))) with (S (Z.to_nat a)).
  2: rewrite Z2Nat.inj_succ //.
  simpl.
  replace (Z.to_nat b - 1 - S (Z.to_nat a))%nat with (Z.to_nat (b - 1 - Z.succ a)).
  rewrite step_inv_step_pow_eq IHa //.
  orewrite Z2Nat.inj_sub.
  replace ((Z.to_nat (Z.succ a))) with (S (Z.to_nat a)).
  2: rewrite Z2Nat.inj_succ //.
  f_equal.
  orewrite Z2Nat.inj_sub.
  reflexivity.
Qed.

Close Scope Z.

(**************************************************************************
 * Reflection tactics
 *)

Ltac reifyValue env t :=
  match t with
  | ?X =>
    let v := lookup X env in
    constr:(R_inv)
  | _ => constr:(R_inv)
  end.

Ltac reifyExpr env t :=
  lazymatch t with
  | pow_fn_rev_Z ?a ?b ?X ?Y =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    constr:(pow_inv (Z.to_nat a) (Z.to_nat b) x y)
  | ?X * ?Y =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    constr:(M_inv x y)
  | Z.pow ?X ?Y =>
    let x := reifyValue env X in
    match Y with
      | Z.pos ?p => constr:(P_inv x p)
      | _ => constr:(P_inv x 1%positive)
    end
  | ?X =>
    let x := reifyValue env X in
    constr:(R_inv)
  end.

Ltac reifyTerm env t :=
  lazymatch t with
   | ?X = ?Y =>
      let x := reifyExpr env X in
      let y := reifyExpr env Y in
      constr:(Eq_inv x y)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    lazymatch xs' with
    | tt => constr:(fun _ : positive => 0%Z)
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ n) xs'' in
      constr:(fun m : positive => if (m =? n)%positive then x else f m)
    end in
  loop (1%positive) xs.

(**************************************************************************
 * User interface tactics
 *)

Open Scope Z.
(* 
Eval compute in Z.pow 2 255 - 21.
Z.pow 2 255 - 21 = 57896044618658097711785492504343953926634992332820282019728792003956564819947
*)

Theorem Inv25519_Z_correct : forall x, Inv25519_Z x = Z.pow x 57896044618658097711785492504343953926634992332820282019728792003956564819947.
Proof.
intros.
  rewrite /Inv25519_Z.
  match goal with
  | [ |- ?X ] =>
    let xss := constr:((x, tt)) in
    let envv := functionalize xss in
    let r1  := reifyTerm xss X in
    pose xs := xss;
    pose env := envv;
    pose reif := r1
    end.
    (* in theory we would use change, but here we need to proceed slightly differently *)
    assert (
      formula_inv_denote (Var 1) {| vars := env |} reif ->
      pow_fn_rev_Z 254 254 x x =
      x ^ 57896044618658097711785492504343953926634992332820282019728792003956564819947).
    {
    subst env reif.
    rewrite /formula_inv_denote pow_inv_pow_fn_rev_eq.
    simpl. trivial.
    }
    apply H ; clear H.
    apply decide_formula_inv_impl.
    (* at this point we don't need any hypothesis, this is purely computational *)
    subst reif ; clears.
    compute.
    reflexivity.
Qed.

Close Scope Z.
