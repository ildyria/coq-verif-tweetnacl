From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.
From Tweetnacl Require Import Low.Reduce_by_P_compose_1.
From Tweetnacl Require Import Low.Reduce_by_P_compose_2.
Require Import ssreflect.
Require Import Recdef.

(*
sv pack25519(u8 *o,const gf n)
{
  int i,j,b;
  gf m,t;
  FOR(i,16) t[i]=n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  FOR(j,2) {
    m[0]=t[0]-0xffed;

    for(i=1;i<15;i++) {
      m[i]=t[i]-0xffff-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }

    for(i=1;i<15;i++) {
      m[i]=t[i];
    }
    for(i=1;i<15;i++) {
      m[i]=m[i]-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }




    m[15]=t[15]-0x7fff-((m[14]>>16)&1);
    b=(m[15]>>16)&1;
    m[14]&=0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]&0xff;
    o[2*i+1]=t[i]>>8;
  }
}
*)

Open Scope Z.

(*****************************************************************************************
 *   DEFINE SEMANTIC
 *)

Section red_expr.

Instance  term_dec : Decidable := 
{
  decide := term_decide;
  denote := term_denote;
  decide_impl := term_decide_impl
}.

Inductive red_expr :=
  | R_red : term -> red_expr
  | Sub_red : red_expr -> red_expr
  | SubC_red : red_expr -> red_expr -> red_expr
  | Mod_red : red_expr -> red_expr
  | Nth_red : nat -> list red_expr -> red_expr -> red_expr.

(* forall (A : Type) (P : list A -> Prop),
       P nil -> (forall (a : A) (l : list A), P l -> P (a :: l)) -> forall l : list A, P l *)
Lemma red_expr_indp : forall (P : red_expr -> Prop),
       (forall t, P (R_red t)) ->
       (forall t, P t -> P (Sub_red t)) ->
       (forall t t', P t -> P t' -> P (SubC_red t t')) ->
       (forall t, P t -> P (Mod_red t)) ->
       (forall l n v, P v -> (forall q, In q l -> P q) ->  P (Nth_red n l v)) ->
       forall l, P l.
Proof.
intros P HR HS HC HM HN.
fix 1.
destruct l ;
first [
   apply HR 
  | apply HS
  | apply HC
  | apply HM
  | apply HN] ; try apply red_expr_indp.
induction l ; intros. inversion H.
simpl in H ; destruct H.
rewrite <- H.
apply red_expr_indp.
apply IHl.
apply H.
Qed.

Fixpoint red_expr_denote env (m : red_expr) : Z :=
  match m with
  | R_red  v  => denote env v
  | Sub_red x => subst_0xffff (red_expr_denote env x)
  | SubC_red x y => subst_c (red_expr_denote env x) (red_expr_denote env y)
  | Mod_red x => mod0xffff (red_expr_denote env x)
  | Nth_red n x v => nth n  (map (red_expr_denote env) x) (red_expr_denote env v)
  end.

Fixpoint red_expr_simplify (l1:red_expr) :red_expr := match  l1 with
  | Nth_red n x v => nth_f red_expr_simplify v n x
  | _ => l1
end.

Lemma red_expr_simplify_denote : forall env l, red_expr_denote env (red_expr_simplify l) = red_expr_denote env l.
Proof.
intros env.
induction l using red_expr_indp ; try reflexivity.
simpl.
rewrite -nth_f_ext map_nth.
destruct (nth_in_or_default n l l0) as [Hi|Hv].
apply H in Hi; assumption.
rewrite Hv; apply IHl.
Qed.


Fixpoint red_expr_decide_rec (l1 l2:red_expr) := match l1, l2 with
  | R_red v1 , R_red v2 => decide v1 v2
  | Sub_red v1, Sub_red v'1 => (red_expr_decide_rec v1 v'1)
  | SubC_red v1 v2, SubC_red v'1 v'2 => andb (red_expr_decide_rec v1 v'1) (red_expr_decide_rec v2 v'2)
  | Mod_red v1, Mod_red v2 => red_expr_decide_rec v1 v2
  | _, _ => false
  end.

Definition red_expr_decide (l1 l2:red_expr) := red_expr_decide_rec (red_expr_simplify l1) (red_expr_simplify l2).
Transparent red_expr_decide.

Lemma red_expr_decide_trans : forall l l', red_expr_decide_rec l l' = true -> red_expr_decide l l' = true.
Proof.
intros.
destruct l, l' ; try assumption ; simpl in H ; discriminate.
Qed.

(* Fixpoint red_expr_decide (l1 l2:red_expr) := match (red_expr_simplify l1), (red_expr_simplify l2) with
  | R_red v1 , R_red v2 => decide v1 v2
  | Sub_red v1, Sub_red v'1 => (red_expr_decide v1 v'1)
  | SubC_red v1 v2, SubC_red v'1 v'2 => andb (red_expr_decide v1 v'1) (red_expr_decide v2 v'2)
  | Mod_red v1, Mod_red v2 => red_expr_decide v1 v2
  | _, _ => false
  end.
 *)

Lemma red_expr_decide_impl:
  forall env l l', 
  red_expr_decide l l' = true ->
  red_expr_denote env l = red_expr_denote env l'.
Proof.
intros env.
induction l using red_expr_indp.
(* case R_red *)
intros.
destruct l'; simpl in H ; try discriminate.
cbn in H ; apply term_decide_impl ; assumption.
cbn in H.
cbn.
rewrite map_nth.

rewrite -nth_f_ext in H.
destruct (nth_in_or_default n l l') as [H'|H'].
destruct (red_expr_simplify (nth n l l')) eqn:? ; try  discriminate.
rewrite -red_expr_simplify_denote Heqr ; simpl.
apply term_decide_impl ; assumption.

rewrite H'.
rewrite H' in H.
destruct (red_expr_simplify l') eqn:? ; try  discriminate.
rewrite -red_expr_simplify_denote Heqr ; simpl.
apply term_decide_impl ; assumption.

(* case Sub_red *)
intros.
destruct l' ; simpl in H ; try discriminate.
cbn in H ; cbn;
apply red_expr_decide_trans in H;
apply IHl in H ; f_equal ; assumption.

cbn in H; rewrite -nth_f_ext in H.
destruct (nth_in_or_default n l0 l') as [H'|H'].
destruct (red_expr_simplify (nth n l0 l')) eqn:? ; try discriminate;
simpl; rewrite map_nth; symmetry ; rewrite -red_expr_simplify_denote Heqr ; symmetry; simpl;
apply red_expr_decide_trans in H;
f_equal; apply IHl ; assumption.

rewrite H' in H.
destruct (red_expr_simplify l') eqn:? ; try discriminate.
simpl; rewrite map_nth; symmetry. rewrite -red_expr_simplify_denote H' Heqr ; symmetry; simpl;
apply red_expr_decide_trans in H;
f_equal; apply IHl ; assumption.

(* case SubC_red *)
intros.
destruct l' ; simpl in H ; try discriminate.
cbn in H ; cbn.
destruct (andb_prop _ _ H)  as [H' H''].
apply red_expr_decide_trans in H'.
apply red_expr_decide_trans in H''.
apply IHl1 in H';
apply IHl2 in H''.
rewrite H' H''.
reflexivity.

cbn in H.
cbn.
rewrite map_nth.

rewrite -nth_f_ext in H.
destruct (nth_in_or_default n l l') as [H3|H3].
destruct (nth n l l') eqn:? ; simpl in * ; try discriminate.
destruct (andb_prop _ _ H)  as [H' H''].
apply red_expr_decide_trans in H'.
apply red_expr_decide_trans in H''.
apply IHl1 in H';
apply IHl2 in H''.
rewrite H' H''.
reflexivity.

rewrite -nth_f_ext in H;
destruct (red_expr_simplify (nth n0 l0 r)) eqn:? => //= .
rewrite map_nth ; simpl ; symmetry ; rewrite -red_expr_simplify_denote Heqr0.
destruct (andb_prop _ _ H)  as [H' H''].
apply red_expr_decide_trans in H'.
apply red_expr_decide_trans in H''.
apply IHl1 in H';
apply IHl2 in H''.
rewrite H' H''.
reflexivity.

rewrite H3.
rewrite H3 in H.
destruct (red_expr_simplify l') eqn:?  => //=;
symmetry;
rewrite -red_expr_simplify_denote Heqr ; simpl.
destruct (andb_prop _ _ H)  as [H' H''].
apply red_expr_decide_trans in H'.
apply red_expr_decide_trans in H''.
apply IHl1 in H';
apply IHl2 in H''.
rewrite H' H''.
reflexivity.

(* case Mod_red *)
intros.
destruct l' ; simpl in H ; try discriminate.
cbn in H ; cbn;
apply red_expr_decide_trans in H;
apply IHl in H ; f_equal ; assumption.

cbn in H; rewrite -nth_f_ext in H.
destruct (nth_in_or_default n l0 l') as [H'|H'].
destruct (red_expr_simplify (nth n l0 l')) eqn:? ; try discriminate;
simpl; rewrite map_nth; symmetry ; rewrite -red_expr_simplify_denote Heqr ; symmetry; simpl;
apply red_expr_decide_trans in H;
f_equal; apply IHl ; assumption.

rewrite H' in H.
destruct (red_expr_simplify l') eqn:? ; try discriminate.
simpl; rewrite map_nth; symmetry. rewrite -red_expr_simplify_denote H' Heqr ; symmetry; simpl;
apply red_expr_decide_trans in H;
f_equal; apply IHl ; assumption.

(* case Nth_red *)

intros l' H'.
simpl.
rewrite map_nth.
destruct (nth_in_or_default n l l0) as [H''|H''].
apply H ; try assumption.
cbn in H' ; rewrite -nth_f_ext in H'; assumption.

rewrite H''.
apply IHl.
cbn in H'.
rewrite -nth_f_ext in H'.
rewrite H'' in H'.
assumption.
Qed.

End red_expr.

Instance  red_expr_dec : Decidable := 
{
  decide := red_expr_decide;
  denote := red_expr_denote;
  decide_impl := red_expr_decide_impl
}.

(*
Fixpoint red_expr_list_denote env (m: list red_expr) : list Z :=
  match m with
  | nil => nil
  | h :: q => (red_expr_denote env h) :: red_expr_list_denote env q
  end.
*)

(*
Lemma red_expr_list_denote_nth :
  forall i env l, red_expr_denote env (nth i l (R_red (Val 0))) = nth i (red_expr_list_denote env l) 0.
Proof.
intros i env l. gen i. induction l as [|h l IHl] ; intros [|i] ; try reflexivity.
simpl. apply IHl.
Qed.
*)
(* 
Lemma red_expr_list_denote_upd_nth :
  forall i env l v, red_expr_list_denote env (upd_nth i l v) = upd_nth i (red_expr_list_denote env l) (red_expr_denote env v).
Proof.
intros i env m. gen i. induction m as [|h m IHm] ; intros [|i] v ; try reflexivity.
simpl. f_equal. apply IHm.
Qed.
 *)
(* Definition formula_red_expr_denote env (t : formula_red_expr) : Prop :=
  match t with
  | Eq_red x y     => red_expr_list_denote env x = red_expr_list_denote env y
  end.

 *)
(*****************************************************************************************
 *   DECIDE EQUALITY
 *)

(* Scheme Equality for red_expr. *)
(* Print term_beq. *)
(* Scheme Equality for list. *)

(* Print red_expr_beq. *)
(* Print list_beq. *)

(* Fixpoint red_expr_decide (l1 l2:red_expr) := match l1, l2 with
  | R_red v1 , R_red v2 => term_eqb v1 v2
  | Sub_red v1, Sub_red v'1 => (decide_red_expr_eq v1 v'1)
  | SubC_red v1 v2, SubC_red v'1 v'2 => andb (decide_red_expr_eq v1 v'1) (decide_red_expr_eq v2 v'2)
  | Mod_red v1, Mod_red v2 => decide_red_expr_eq v1 v2
  | _, _ => false
  end.

Fixpoint decide_red_expr_list_eq (l1 l2:list red_expr) := match l1, l2 with
  | nil, nil => true
  | h1 :: q1, h2 :: q2 => andb (decide_red_expr_eq h1 h2) (decide_red_expr_list_eq q1 q2)
  | _, _ => false
end.

 *)

(* Lemma decide_red_expr_list_eq_impl:
  forall env l l',
  decide_red_expr_list_eq l l' = true ->
  red_expr_list_denote env l = red_expr_list_denote env l'.
Proof.
intros env.
induction l ; destruct l' ; intros ; simpl in *; 
repeat match goal with
  | _ => discriminate
  | _ => reflexivity
  | [ H : _ && _ = true |- _ ] => apply andb_prop in H; destruct H
  | [ H : _ , H1 : _ |- _ ] => apply H in H1 (* why bother ? :D *)
  | [ env: environment, H : decide_red_expr_eq _ _  = true |- _ ] => apply (decide_red_expr_eq_impl env) in H
  | [ H : _ = _ |- _ ] => rewrite H
  | [ H : False |- _ ] => destruct H
end.
Qed. *)

(* Definition decide_formula_red_expr (f : formula_red_expr) : bool := match f with
  | Eq_red x y => decide_red_expr_list_eq x y
  end.
 *)
(* Lemma decide_formula_red_impl : forall env f, decide_formula_red_expr f = true -> formula_red_expr_denote env f.
Proof. intros env [? ?]. by apply decide_red_expr_list_eq_impl. Qed.
 *)
(* Weaponize our expression so we can translate functions *)

Instance list_red_expr : Decidable :=
{
  decide := list_upd_ext_decide red_expr_dec;
  denote := list_upd_ext_denote red_expr_dec;
  decide_impl := list_upd_ext_decide_impl red_expr_dec
}.

Definition sub_red_step (a:Z) (m t:list red_expr) : list red_expr :=
    let m' := nth (Z.to_nat (a - 1)) m (R_red (Val 0)) in
    let t' := nth (Z.to_nat a) t (R_red (Val 0)) in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (SubC_red (Sub_red t') m')) (Mod_red m').

Definition sub_red_step_1 (a:Z) (m t:list red_expr) : list red_expr :=
    let t' := nth (Z.to_nat a) t (R_red (Val 0)) in
      (upd_nth (Z.to_nat a) m (Sub_red t')).

Definition sub_red_step_2 (a:Z) (m:list red_expr) : @list_upd_ext red_expr :=
    let m' := Nth_red (Z.to_nat (a - 1)) m (R_red (Val 0)) in
    let t' := Nth_red (Z.to_nat a) m (R_red (Val 0)) in
      Upd (Z.to_nat (a-1)) (Upd (Z.to_nat a) m (SubC_red t' m')) (Mod_red m').


Lemma step_fn_red_expr : forall env a m t,
  sub_fn_rev sub_step a (red_expr_list_denote env m) (red_expr_list_denote env t) =
  red_expr_list_denote env (sub_fn_rev sub_red_step a m t).
Proof.
intros env [ | p | p] m t.
all: try reflexivity.
assert(Hi:= Pos2Z.is_nonneg p).
remember (Z.pos p) as i.
clears p.
gen m t.
apply (natlike_ind (fun i => ∀ m t : list red_expr,
sub_fn_rev sub_step i (red_expr_list_denote env m) (red_expr_list_denote env t) =
red_expr_list_denote env (sub_fn_rev sub_red_step i m t))) ; try omega.
intros ; reflexivity.
clears i.
intros i Hi IH m t.
assert(Hii: i = 0 \/ 0 < i) by omega.
change (Z.succ i) with (i + 1).
destruct Hii as [Hii|Hii] ; try (subst i ; reflexivity).
rewrite sub_fn_rev_n.
symmetry.
rewrite sub_fn_rev_n.
symmetry.
replace (i + 1 - 1) with i.
all: try omega.
unfold sub_red_step.
rewrite ?red_expr_list_denote_upd_nth.
unfold sub_step.
rewrite ?red_expr_list_denote_nth. simpl.
unfold subst_0xffffc, subst_c, subst_0xffff.
rewrite IH.
rewrite ?red_expr_list_denote_nth.
reflexivity.
Qed.

Lemma step_fn_red_expr_1 : forall env a m t,
  sub_fn_rev sub_step_1 a (red_expr_list_denote env m) (red_expr_list_denote env t) =
  red_expr_list_denote env (sub_fn_rev sub_red_step_1 a m t).
Proof.
intros env [ | p | p] m t.
all: try reflexivity.
(* pattern p. *)
(* induction p using Pos.peano_ind. *)
assert(Hi:= Pos2Z.is_nonneg p).
remember (Z.pos p) as i.
clears p.
gen m t.
(* Check nat_ind.
About natlike_ind.
Locate natlike_ind.
SearchAbout positive "peano".
Axiom natlike_ind' : forall P : forall (z : Z) (pf : 0 <= z), Prop, (forall pf, P 0 pf) -> (forall z pf pf', P z pf -> P (Z.succ z) pf') -> forall z pf, P z pf.
induction i,Hi using natlike_ind'.
induction i,Hi using natlike_ind.
induction Hi,i using natlike_ind. *)
(* gen Hi. *)
pattern i.
apply natlike_ind ;try omega.
(* match goal with 
  | [ |- ?f p ] => apply (natlike_ind f)
end.

apply (natlike_ind (fun i => ∀ m t : list red_expr,
sub_fn_rev sub_step_1 i (red_expr_list_denote env m) (red_expr_list_denote env t) =
red_expr_list_denote env (sub_fn_rev sub_red_step_1 i m t))) ; try omega.
 *)
intros ; reflexivity.
clears i.
intros i Hi IH m t.
assert(Hii: i = 0 \/ 0 < i) by omega.
change (Z.succ i) with (i + 1).
destruct Hii as [Hii|Hii] ; try (subst i ; reflexivity).
rewrite sub_fn_rev_n.
symmetry.
rewrite sub_fn_rev_n.
symmetry.
replace (i + 1 - 1) with i.
all: try omega.
unfold sub_red_step_1.
rewrite ?red_expr_list_denote_upd_nth.
unfold sub_step_1.
rewrite ?red_expr_list_denote_nth. simpl.
unfold subst_0xffffc, subst_c, subst_0xffff.
rewrite IH.
rewrite ?red_expr_list_denote_nth.
reflexivity.
Qed.

Lemma step_fn_red_expr_2 : forall env a m,
  sub_fn_rev_s sub_step_2 a (red_expr_list_denote env m) =
  red_expr_list_denote env (sub_fn_rev_s sub_red_step_2 a m).
Proof.
intros env [ | p | p] m.
all: try reflexivity.
assert(Hi:= Pos2Z.is_nonneg p).
remember (Z.pos p) as i.
clears p.
gen m.
apply (natlike_ind (fun i => ∀ m : list red_expr,
sub_fn_rev_s sub_step_2 i (red_expr_list_denote env m) =
red_expr_list_denote env (sub_fn_rev_s sub_red_step_2 i m))) ; try omega.
intros ; reflexivity.
clears i.
intros i Hi IH m.
assert(Hii: i = 0 \/ 0 < i) by omega.
change (Z.succ i) with (i + 1).
destruct Hii as [Hii|Hii] ; try (subst i ; reflexivity).
rewrite sub_fn_rev_s_n.
symmetry.
rewrite sub_fn_rev_s_n.
symmetry.
replace (i + 1 - 1) with i.
all: try omega.
unfold sub_red_step_2.
rewrite ?red_expr_list_denote_upd_nth.
unfold sub_step_2.
rewrite ?red_expr_list_denote_nth. simpl.
unfold subst_0xffffc, subst_c, subst_0xffff.
rewrite IH.
rewrite ?red_expr_list_denote_nth.
reflexivity.
Qed.

Close Scope Z.


(**************************************************************************
 * Reflection tactics
 *)

Ltac allVars_red xs e :=
  match e with
  | ?X  = ?Y =>
    let xs := allVars_red xs X in
    allVars_red xs Y
  | sub_fn_rev_s _ _ ?X =>
    allVars_red xs X
  | sub_fn_rev _ _ ?X ?Y =>
    let xs := allVars_red xs X in
    allVars_red xs Y
  | upd_nth _ ?X ?Y =>
    let xs := allVars_red xs X in
    allVars_red xs Y
  | nth _ ?X ?Y =>
    let xs := allVars_red xs X in
    allVars_red xs Y
  | ?X :: ?Y =>
    let xs := allVars_red xs X in
    allVars_red xs Y
  | nil => xs
  | ?X => allVar xs X
  | _ => xs
  end.

Ltac gather_vars_red :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars_red tt X in
     pose xs
  end.

Ltac reifyValue_red env t :=
  match t with
  | ?X =>
    let v := lookup X env in
    constr:(Var v)
  | _ => constr:(Val t)
  end.

Ltac reifyExpr_red env t :=
  lazymatch t with
  | sub_fn_rev_s sub_step_2 ?a ?X =>
    let x := reifyExpr_red env X in
    constr:(sub_fn_rev_s sub_red_step_2 a x)
  | sub_fn_rev sub_step_1 ?a ?X ?Y =>
    let x := reifyExpr_red env X in
    let y := reifyExpr_red env Y in
    constr:(sub_fn_rev sub_red_step_1 a x y)
  | sub_fn_rev sub_step ?a ?X ?Y =>
    let x := reifyExpr_red env X in
    let y := reifyExpr_red env Y in
    constr:(sub_fn_rev sub_red_step a x y)
  | upd_nth ?a ?X ?Y =>
    let x := reifyExpr_red env X in
    let y := reifyExpr_red env Y in
    constr:(upd_nth a x y)
  | nth ?a ?X ?Y =>
    let x := reifyExpr_red env X in
    let y := reifyExpr_red env Y in
    constr:(nth a x y)
  | ?X :: ?Y =>
    let x := reifyExpr_red env X in
    let y := reifyExpr_red env Y in
    constr:((R_red x) :: y)
  | nil => constr:(nil:list red_expr)
  | ?X =>
    let x := reifyValue_red env X in
    constr:(x)
  end.

Ltac reifyTerm_red env t :=
  lazymatch t with
   | ?X = ?Y =>
      let x := reifyExpr_red env X in
      let y := reifyExpr_red env Y in
      constr:(Eq_red x y)
  end.

Ltac functionalize_red xs :=
  let rec loop_red n xs' :=
    lazymatch xs' with
    | tt => constr:(fun _ : positive => 0%Z)
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop_red (Pos.succ n) xs'' in
      constr:(fun m : positive => if (m =? n)%positive then x else f m)
    end in
  loop_red (1%positive) xs.

(**************************************************************************
 * User interface tactics
 *)

Open Scope Z.

Lemma sub_fn_rev_f_g :  forall a m t,
  (length m = 16)%nat ->
  (length t = 16)%nat ->
  0 < a < 16 ->
  sub_fn_rev sub_step a m t = sub_fn_rev_s sub_step_2 a (sub_fn_rev sub_step_1 a m t).
Proof.
intros a m t Hm Ht Ha.
intros.
do 17 (destruct m ; [tryfalse |]) ; [|tryfalse].
do 17 (destruct t ; [tryfalse |]) ; [|tryfalse].
(* gather_vars_red. *)
assert_gen_hyp_ H a 15 14 ; try omega.
match goal with
  | [ |- ?X ] =>
    let xss  := allVars_red tt X in
    let envv := functionalize_red xss in
    let r1  := reifyTerm_red xss X in
    pose xss;
    pose envv;
    pose r1
    end.
    rename p into xs.
    rename z31 into env.
    rename f into reif.
    (* in theory we would use change, but here we need to proceed slightly differently *)
    assert (Hsubst:
      formula_red_expr_denote {| vars := env |} reif ->
      sub_fn_rev sub_step a [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30] =
sub_fn_rev_s sub_step_2 a
  (sub_fn_rev sub_step_1 a [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29; z30])).
    {
    subst reif.
    unfold formula_red_expr_denote.
    rewrite <- step_fn_red_expr.
    rewrite <- step_fn_red_expr_2.
    rewrite <- step_fn_red_expr_1.
    subst env.
    trivial.
    }
apply Hsubst.
apply decide_formula_red_impl.
clear Hsubst.
clear xs.
clear env.
subst reif.
clear Hm Ht. clears.
repeat match goal with
  | [ H : ?a = _ |- _ ] => subst a ; compute ; reflexivity
  | [ H : _ \/ _ |- _ ] => destruct H
end.
Qed.

Close Scope Z.