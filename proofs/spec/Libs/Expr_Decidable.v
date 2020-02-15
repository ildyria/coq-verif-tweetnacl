Set Warnings "-notation-overridden".

Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Import Coq.Sorting.Sorting Orders.
Require Import ssreflect.
Require Import Tweetnacl.Libs.Decidable.
Require Import Tweetnacl.Libs.Term_Decidable.

Open Scope Z_scope.

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
      | false => match term_decide a b with
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
  destruct(term_decide a b) eqn:H2; destruct(term_decide b a) eqn:H3.
  auto.
  move: H3 ; rewrite term_decide_com; congruence.
  move: H3 ; rewrite term_decide_com; congruence.
  exfalso.
  clear IHa.
  unfold term_ltb, term_decide in *.
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
Module Import ListTermSort := Sort ListTermOrder.

Local Instance term_dec : Decidable := 
{
  decide := term_decide;
  denote := term_denote;
  decide_impl := term_decide_impl
}.

Section Expr.
  Inductive expr :=
    | R : term -> expr
    | A : expr -> expr -> expr
    | M : term -> term -> expr.

  Fixpoint expr_denote (env:environment) (m : expr) : Z :=
    match m with
    | R v   => denote env v
    | A x y => expr_denote env x + expr_denote env y
    | M x y => denote env x * denote env y
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

  Fixpoint ldenote_M (env:environment) (ls : list term) : Z :=
    match ls with
      | nil => 1
      | x :: ls' => denote env x * (ldenote_M env ls')
    end.

  Local Lemma ldenote_M_cons: forall (env:environment) a l, ldenote_M env (a::l) =  (denote env a) * ldenote_M env l.
  Proof. by move=> //. Qed.

  Local Lemma ldenote_M_app: forall (env:environment) a b, ldenote_M env (a ++ b) = ldenote_M env a * ldenote_M env b.
  Proof. induction a ; intros ; simpl => //.
  destruct (ldenote_M env b) ; auto.
  rewrite IHa ; ring.
  Qed.

  Local Lemma ldenote_M_simplify: forall (env:environment)  l, ldenote_M env l = ldenote_M env (simplify_M l).
  Proof. induction l as [|h l IHl] => //=.
  rewrite IHl. destruct h. by destruct p.
  destruct z ; try destruct p ; try reflexivity.
  simpl term_denote. ring.
  Qed.

  Local Lemma simplifiy_M_0 : forall (env:environment) a, existsb (decide (Val 0)) a = true -> ldenote_M env a = 0.
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
      match existsb (decide (Val 0)) s with
      | true => simplify_A q
      | false => s :: simplify_A q
      end
    end.

  Fixpoint ldenote (env:environment) (ls : list (list term)) : Z :=
    match ls with
      | nil => 0
      | x :: ls' => (ldenote_M env x) + (ldenote env ls')
    end.

  Local Lemma ldenote_cons: forall (env:environment) a l, ldenote env (a::l) = (ldenote_M env a) + ldenote env l.
  Proof. by move=> //. Qed.

  Local Lemma ldenote_app: forall (env:environment) a b, ldenote env (a ++ b) = ldenote env a + ldenote env b.
  Proof.
  induction a ; intros ; simpl => //.
  rewrite IHa ; ring.
  Qed.

  Local Lemma latten_expr_correct : forall (env:environment)  t, expr_denote env t = ldenote env (latten_expr t).
  Proof.
  induction t ; simpl ; try ring.
  rewrite ldenote_app IHt1 IHt2 => //.
  Qed.

  Local Lemma ldenote_simplify: forall (env:environment)  l, ldenote env l = ldenote env (simplify_A l).
  Proof. induction l ; intros ; simpl => //.
  destruct (existsb (term_decide (Val 0)) (simplify_M a)) eqn:H; auto.
  apply (simplifiy_M_0 env) in H.
  move: H ; rewrite -ldenote_M_simplify => -> ; omega.
  simpl; rewrite -?ldenote_M_simplify; omega.
  Qed.

  Definition flatten_expr t := simplify_A (latten_expr t).

  Local Lemma flatten_expr_correct : forall (env:environment) t, expr_denote env t = ldenote env (flatten_expr t).
  Proof. move => env t. unfold flatten_expr.
  rewrite -ldenote_simplify.
  apply latten_expr_correct.
  Qed.

(*****************************************************************************************
 *   SORT THE LIST
 *)


  Local Lemma perm_ldenote_M : forall (env:environment)  l l', Permutation.Permutation l l' -> ldenote_M env l = ldenote_M env l'.
  Proof.
    intros env l l' H.
    induction H => // ; simpl.
    by rewrite IHPermutation.
    ring.
    by rewrite IHPermutation1 IHPermutation2.
  Qed.

  Local Lemma sort_ldenote_M : forall (env:environment) l, ldenote_M env l = ldenote_M env (TermSort.sort l).
  Proof.
    intros.
    apply perm_ldenote_M.
    apply TermSort.Permuted_sort.
  Qed.

  Definition flatten_eq l := ListTermSort.sort (map TermSort.sort l).

  Local Lemma perm_ldenote : forall (env:environment)  l l', Permutation.Permutation l l' -> ldenote env l = ldenote env l'.
  Proof.
    intros env  l l' H.
    induction H => // ; simpl.
    by rewrite IHPermutation.
    ring.
    by rewrite IHPermutation1 IHPermutation2.
  Qed.

  Local Lemma sort_ldenote : forall (env:environment)  l, ldenote env l = ldenote env (ListTermSort.sort l).
  Proof.
    intros.
    apply perm_ldenote.
    apply Permuted_sort.
  Qed.

  Theorem flatten_eq_denote : forall (env:environment)  l, ldenote env l = ldenote env (flatten_eq l).
  Proof.
    induction l => //.
    unfold flatten_eq in *.
    rewrite -sort_ldenote.
    simpl.
    f_equal.
    apply sort_ldenote_M.
    by rewrite -sort_ldenote in IHl.
  Qed.

(*****************************************************************************************
 *   DECIDE EQUALITY
 *)

  Fixpoint decide_list_term_eq (l l':list term): bool := match l, l' with
    | nil , nil => true
    | a:: qa , b :: qb => andb (decide a b) (decide_list_term_eq qa qb)
    | _, _ => false
    end.

  Local Lemma decide_list_term_eq_impl:
    forall (env:environment) l l', 
    decide_list_term_eq l l' = true ->
    ldenote_M env l = ldenote_M env l'.
  Proof.
  induction l ; destruct l' ; auto => H.
  simpl in H ; discriminate.
  simpl in H ; discriminate.
  simpl in *.
  move: H; rewrite !Bool.andb_true_iff ; move=> [Ht Hl].
  apply IHl in Hl.
  f_equal.
  apply term_decide_impl.
  all: assumption.
  Qed.

  Local Fixpoint decide_list_list_term (l l':list (list term)) : bool := match l, l' with
    | nil, nil => true
    | a:: qa , b :: qb => andb (decide_list_term_eq a b) (decide_list_list_term qa qb)
    | _, _ => false
    end.

  Local Lemma decide_list_list_term_eq_impl : forall (env:environment)  l l', decide_list_list_term l l' = true ->
    ldenote env l = ldenote env l'.
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

Definition expr_decide (e e': expr) : bool := decide_llt (flatten_expr e) (flatten_expr e').

Lemma expr_decide_impl:
  forall (env:environment) a b,
    expr_decide a b = true ->
    expr_denote env a = expr_denote env b.
Proof.
  intros env a b Hdec.
  unfold expr_decide in Hdec.
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

End Expr.

Local Definition ta := Var 1%positive.
Local Definition tb := Var 2%positive.
Local Definition tc := Var 3%positive.
Local Definition td := Var 4%positive.
Local Definition te := Var 5%positive.
Local Definition tf := Var 6%positive.
Local Definition tg := Var 7%positive.

Local Definition expr1 := A (M ta tb) (A (R tc) (R tb)).
Local Definition expr2 := A (A (R tc) (R tb)) (M ta tb).

Local Instance expr_dec : Decidable := Build_Decidable expr Z expr_decide (expr_denote) expr_decide_impl.

Local Example test1 : expr_decide expr1 expr2 = true.
Proof.
by compute.
Qed.

Close Scope Z.