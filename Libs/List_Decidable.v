Set Warnings "-notation-overridden".

Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Import Coq.Sorting.Sorting Orders.
Require Import ssreflect.

Record environment := { vars : positive -> Z }.

Open Scope Z_scope.

Inductive term :=
  | Var   : positive -> term
  | Val   : Z -> term
  .

Inductive expr :=
  | R : term -> expr
  | A : expr -> expr -> expr
  | M : term -> term -> expr.

Inductive formula := 
  | Eq : expr -> expr -> formula
  | LEq : list expr -> list expr -> formula.

Definition term_eqb (x y : term) : bool := match x , y with
  | Var x , Var y => Pos.eqb x y
  | Val x,  Val y => Z.eqb x y
  | _ , _ => false
  end.

Lemma term_eqb_com : forall x y, term_eqb x y = term_eqb y x.
Proof.
move => [] a [] b //=.
rewrite ?Pos2Z.inj_eqb.
apply Z.eqb_sym.
apply Z.eqb_sym.
Qed.

Lemma term_eqb_refl : forall x y, term_eqb x y = true <-> x = y.
Proof.
move => x y ; rewrite /term_eqb ; split => H ; simpl.
destruct x,y; move: H.
rewrite Pos.eqb_eq => -> //.
discriminate.
discriminate.
rewrite Z.eqb_eq => -> //.
subst ; destruct y.
rewrite Pos.eqb_eq //.
rewrite Z.eqb_eq //.
Qed.


Definition term_leb (x y : term) : bool := match x , y with
  | Var x , Var y => Pos.leb x y
  | Val x , Val y => Z.leb x y
  | Var x,  Val y => false
  | Val x,  Var y => true
  end.

Definition term_ltb (x y : term) : bool := match x , y with
  | Var x , Var y => Pos.ltb x y
  | Val x , Val y => Z.ltb x y
  | Var x,  Val y => false
  | Val x,  Var y => true
  end.

Definition term_denote env (x : term) : Z :=
  match x with
  | Var n => vars env n
  | Val n => n
  end.

Fixpoint expr_denote env (m : expr) : Z :=
  match m with
  | R v   => term_denote env v
  | A x y => (expr_denote env x + expr_denote env y)%Z
  | M x y => (term_denote env x * term_denote env y)%Z
  end.

Fixpoint list_expr_denote env (l: list expr) : list Z :=
  match l with
    | nil => nil
    | h :: q => (expr_denote env h) :: list_expr_denote env q
  end.

Definition formula_denote env (t : formula) : Prop :=
  match t with
  | Eq x y     => expr_denote env x = expr_denote env y
  | LEq x y    => list_expr_denote env x = list_expr_denote env y
  end.

Fixpoint latten_expr (e : expr) : (list (list term)) := match e with
  | A a b => latten_expr a ++ latten_expr b
  | M a b => (a :: b :: nil) :: nil
  | R x => (x :: nil) :: nil
end.

Fixpoint simplify_M (l: list term) : list term := match l with
  | nil => nil
  | Val 1 :: q => simplify_M q
  | h :: q => h :: simplify_M q
  end.

Fixpoint ldenote_M env (ls : list term) : Z :=
  match ls with
    | nil => 1
    | x :: ls' => term_denote env x * (ldenote_M env ls')
  end.

Lemma ldenote_M_cons: forall env a l, ldenote_M env (a::l) = (term_denote env a) * ldenote_M env l.
Proof. by move=> //. Qed.

Lemma ldenote_M_app: forall env a b, ldenote_M env (a ++ b) = ldenote_M env a * ldenote_M env b.
Proof. induction a ; intros ; simpl => //.
destruct (ldenote_M env b) ; auto.
rewrite IHa ; ring.
Qed.

Lemma ldenote_M_simplify: forall env l, ldenote_M env l = ldenote_M env (simplify_M l).
Proof. induction l as [|h l IHl] => //=.
rewrite IHl. destruct h. by destruct p.
destruct z ; try destruct p ; try reflexivity.
simpl term_denote ; omega.
Qed.

Lemma simplifiy_M_0 : forall env a, existsb (term_eqb (Val 0)) a = true -> ldenote_M env a = 0.
Proof.
induction a => //=.
rewrite Bool.orb_true_iff => H.
case H ; clear H => H.
destruct a ; try discriminate.
destruct z ; try discriminate.
simpl term_denote ; omega.
apply IHa in H ; rewrite H ; omega.
Qed.

Fixpoint simplify_A (l :list (list term)) : list (list term) := match l with
  | nil => nil
  | h :: q => let s := simplify_M h in
    match existsb (term_eqb (Val 0)) s with
    | true => simplify_A q
    | false => s :: simplify_A q
    end
  end.

Fixpoint ldenote env (ls : list (list term)) : Z :=
  match ls with
    | nil => 0
    | x :: ls' => (ldenote_M env x) + (ldenote env ls')
  end.

Lemma ldenote_cons: forall env a l, ldenote env (a::l) = (ldenote_M env a) + ldenote env l.
Proof. by move=> //. Qed.

Lemma ldenote_app: forall env a b, ldenote env (a ++ b) = ldenote env a + ldenote env b.
Proof.
induction a ; intros ; simpl => //.
rewrite IHa ; ring.
Qed.

Lemma latten_expr_correct : forall env t, expr_denote env t = ldenote env (latten_expr t).
Proof.
induction t ; simpl ; try ring.
rewrite ldenote_app IHt1 IHt2 => //.
Qed.

Lemma ldenote_simplify: forall env l, ldenote env l = ldenote env (simplify_A l).
Proof. induction l ; intros ; simpl => //.
destruct (existsb (term_eqb (Val 0)) (simplify_M a)) eqn:H; auto.
apply (simplifiy_M_0 env) in H.
move: H ; rewrite -ldenote_M_simplify => -> ; omega.
simpl; rewrite -?ldenote_M_simplify. omega.
Qed.

Definition flatten_expr t := simplify_A (latten_expr t).

Lemma flatten_expr_correct : forall env t, expr_denote env t = ldenote env (flatten_expr t).
Proof. move => env t. unfold flatten_expr.
rewrite -ldenote_simplify.
apply latten_expr_correct.
Qed.

(*****************************************************************************************
 *   SORT THE LIST
 *)

Module TermOrder <: TotalLeBool.
  Definition t := term.
  Definition leb x y := term_leb x y.

  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    move=> a b.
    unfold leb, term_leb.
    destruct a, b.
    rewrite !Pos2Z.inj_leb.
    assert(H:= Zle_bool_total (Z.pos p) (Z.pos p0)).
    destruct H as [H|H] ; rewrite H ; auto.
    by right.
    by left.
    assert(H:= Zle_bool_total z z0).
    destruct H as [H|H] ; rewrite H ; auto.
  Qed.

End TermOrder.

Module ListTermOrder <: TotalLeBool.
  Definition t := list term.

  Fixpoint leb x y := match x, y with
    | nil , _ => true
    | _ , nil => false
    | a :: qa, b :: qb => match term_ltb a b with
      | true => true
      | false => match term_eqb a b with
        | true => leb qa qb
        | false => false
        end
      end
  end.

  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
  elim => [| a qa IHa].
  by left.
  move=> [| b qb] ; simpl.
  by right.
  specialize IHa with qb ; simpl.
  destruct(term_ltb a b) eqn:H0 ; destruct(term_ltb b a) eqn:H1.
  by left.
  by left.
  by right.
  destruct(term_eqb a b) eqn:H2; destruct(term_eqb b a) eqn:H3.
  auto.
  move: H3 ; rewrite term_eqb_com; congruence.
  move: H3 ; rewrite term_eqb_com; congruence.
  exfalso.
  clear IHa.
  unfold term_ltb, term_eqb in *.
  destruct a, b ; try discriminate.
  move: H2 ; rewrite Pos2Z.inj_eqb Z.eqb_neq.
  move: H0 ; rewrite Pos2Z.inj_ltb Z.ltb_ge.
  move: H1 ; rewrite Pos2Z.inj_ltb Z.ltb_ge.
  move => ? ? ?.
  omega.
  move: H2 ; rewrite Z.eqb_neq.
  move: H0 ; rewrite Z.ltb_ge.
  move: H1 ; rewrite Z.ltb_ge.
  move => ? ? ?.
  omega.
  Qed.
End ListTermOrder.

Module Import TermSort := Sort TermOrder.

Lemma perm_ldenote_M : forall env l l', Permutation.Permutation l l' -> ldenote_M env l = ldenote_M env l'.
Proof.
  intros env l l' H.
  induction H => // ; simpl.
  by rewrite IHPermutation.
  ring.
  by rewrite IHPermutation1 IHPermutation2.
Qed.

Lemma sort_ldenote_M : forall env l, ldenote_M env l = ldenote_M env (TermSort.sort l).
Proof.
  intros.
  apply perm_ldenote_M.
  apply Permuted_sort.
Qed.

Module Import ListTermSort := Sort ListTermOrder.

Definition flatten_eq l := ListTermSort.sort (map TermSort.sort l).

Lemma perm_ldenote : forall env l l', Permutation.Permutation l l' -> ldenote env l = ldenote env l'.
Proof.
  intros env l l' H.
  induction H => // ; simpl.
  by rewrite IHPermutation.
  ring.
  by rewrite IHPermutation1 IHPermutation2.
Qed.

Lemma sort_ldenote : forall env l, ldenote env l = ldenote env (ListTermSort.sort l).
Proof.
  intros.
  apply perm_ldenote.
  apply Permuted_sort.
Qed.

Theorem flatten_eq_denote : forall env l, ldenote env l = ldenote env (flatten_eq l).
Proof.
  induction l => //.
  unfold flatten_eq in *.
  rewrite -sort_ldenote.
  simpl.
  f_equal.
  apply sort_ldenote_M.
  by rewrite -sort_ldenote in IHl.
Qed.

Local Definition ta := Var 1%positive.
Local Definition tb := Var 2%positive.
Local Definition tc := Var 3%positive.
Local Definition td := Var 4%positive.
Local Definition te := Var 5%positive.
Local Definition tf := Var 6%positive.
Local Definition tg := Var 7%positive.

Local Definition expr1 := A (M ta tb) (A (R tc) (R tb)).
Local Definition expr2 := A (A (R tc) (R tb)) (M ta tb).
(* Eval compute in flatten_expr expr1. *)
(* Eval compute in flatten_eq (flatten_expr expr1). *)
(* Eval compute in (flatten_expr expr2). *)
(* Eval compute in flatten_eq (flatten_expr expr2). *)




(*****************************************************************************************
 *   DECIDE EQUALITY
 *)

Fixpoint decide_list_term_eq (l l':list term): bool := match l, l' with
  | nil , nil => true
  | a:: qa , b :: qb => andb (term_eqb a b) (decide_list_term_eq qa qb)
  | _, _ => false
  end.

Lemma decide_list_term_eq_impl:
  forall env l l', 
  decide_list_term_eq l l' = true ->
  ldenote_M env l = ldenote_M env l'.
Proof.
induction l ; destruct l' ; auto => H.
simpl in H ; discriminate.
simpl in H ; discriminate.
simpl in *.
move: H; rewrite !Bool.andb_true_iff ; move=> [Ht Hl].
apply IHl in Hl.
move: Ht ; rewrite term_eqb_refl => -> ; rewrite Hl ; reflexivity.
Qed.

Fixpoint decide_list_list_term (l l':list (list term)) : bool := match l, l' with
  | nil, nil => true
  | a:: qa , b :: qb => andb (decide_list_term_eq a b) (decide_list_list_term qa qb)
  | _, _ => false
  end.

Lemma decide_list_list_term_eq_impl : forall env l l', decide_list_list_term l l' = true -> ldenote env l = ldenote env l'.
Proof.
induction l ; destruct l' ; auto => H.
simpl in H ; discriminate.
simpl in H ; discriminate.
simpl in *.
move: H; rewrite !Bool.andb_true_iff ; move=> [Ht Hl].
apply IHl in Hl.
apply (decide_list_term_eq_impl env) in Ht.
rewrite Ht Hl ; reflexivity.
Qed.

Definition decide_llt (l l':list (list term)) : bool := decide_list_list_term (flatten_eq l) (flatten_eq l').

Definition decide_expr (e e': expr) : bool := decide_llt (flatten_expr e) (flatten_expr e').

Lemma decidable_expr:
  forall env a b,
    decide_expr a b = true ->
    expr_denote env a = expr_denote env b.
Proof.
  intros env a b Hdec.
  unfold decide_expr in Hdec.
  unfold decide_llt in Hdec.
  assert(H: exists l, l = flatten_expr a).
    eexists. reflexivity.
  destruct H as [l Hl].
  assert(Hld: ldenote env l = expr_denote env a).
    rewrite flatten_expr_correct; subst => //.
  assert(H: exists l, l = flatten_expr b).
    eexists. reflexivity.
  destruct H as [l' Hl'].
  assert(Hl'd: ldenote env l' = expr_denote env b).
    rewrite flatten_expr_correct; subst => //.
  rewrite -Hld -Hl'd.
  rewrite flatten_eq_denote ; symmetry ; rewrite flatten_eq_denote ; symmetry ; subst.
  by apply decide_list_list_term_eq_impl.
Qed.

Local Example test1 : decide_llt (flatten_expr expr1) (flatten_expr expr2) = true.
Proof.
by compute.
Qed.

Fixpoint decide_list (l l' : list expr) : bool := match l, l' with
  | nil, nil => true
  | a :: qa , b :: qb => andb (decide_expr a b) (decide_list qa qb)
  | _, _ => false
  end.

Lemma decidable_list_expr:
  forall env a b,
    decide_list a b = true ->
    list_expr_denote env a = list_expr_denote env b.
Proof.
  induction a as [|a qa IHa] => b H.
  destruct b.
  reflexivity.
  simpl in H ; congruence.
  destruct b.
  simpl in H ; congruence.
  simpl in *.
  apply Bool.andb_true_iff in H.
  destruct H.
  f_equal.
  by apply decidable_expr.
  by apply IHa.
Qed.

Definition decide_formula (f : formula) : bool := match f with
  | Eq x y => decide_expr x y
  | LEq x y => decide_list x y
  end.

Lemma decide_formula_impl : forall env f, decide_formula f = true -> formula_denote env f.
Proof. move=> env [? ?| ? ?]. by apply decidable_expr. by apply decidable_list_expr. Qed.


(********************************************************************************)

Local Example test2: decide_formula (Eq expr1 expr2) = true.
Proof.
by compute.
Qed.

Local Example test3: decide_formula (LEq (expr1::nil) (expr2::nil)) = true.
Proof.
by compute.
Qed.

Close Scope Z.