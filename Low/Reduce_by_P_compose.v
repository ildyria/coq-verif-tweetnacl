(* From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export. *)
(* From Tweetnacl Require Import Mid.SubList. *)
(* From Tweetnacl Require Import Low.Get_abcdef. *)
(* From Tweetnacl Require Import Low.GetBit_pack25519. *)
(* From Tweetnacl Require Import Low.Sel25519. *)
(* From Tweetnacl Require Import Low.Constant. *)
From Tweetnacl Require Import Libs.Lists_extended.
From Tweetnacl Require Import Libs.List_Ltac.
From Tweetnacl Require Import Libs.LibTactics_SF.
From Tweetnacl Require Import Libs.LibTactics.
From stdpp Require Import prelude.
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
(*
0xffff = 65535
0xffed = 65517
0x7fff = 32767
*)

Definition subst_0xffed t := t - 65517.
Definition subst_0xffffc t m := t - 65535 - (Z.land (Z.shiftr m 16) 1).
Definition subst_0xffff t := t - 65535.
Definition subst_0x7fffc t m := t - 32767 - (Z.land (Z.shiftr m 16) 1).
Definition subst_0x7fff t := t - 32767.
Definition subst_c t m := t - (Z.land (Z.shiftr m 16) 1).
Definition mod0xffff m := Z.land m 65535.

Definition sub_step (a:Z) (m t:list Z) : list Z :=
    let m' := nth (Z.to_nat (a - 1)) m 0 in
    let t' := nth (Z.to_nat a) t 0 in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (subst_0xffffc t' m')) (mod0xffff m').

Lemma nth_i_1_substep: forall i m t, 
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  nth (Z.to_nat (i - 1)) (sub_step i m t) 0 = mod0xffff (nth (Z.to_nat (i - 1)) m 0).
Proof.
  intros i m t Hmt Him.
  unfold sub_step, mod0xffff.
  rewrite upd_nth_same_Zlength ; try reflexivity.
  split ; try omega ; rewrite upd_nth_Zlength ; rewrite Z2Nat.id ; try omega.
Qed.

Lemma nth_i_substep: forall i m t, 
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  nth (Z.to_nat (i)) (sub_step i m t) 0 = subst_0xffffc (nth (Z.to_nat i) t 0) (nth (Z.to_nat (i - 1)) m 0).
Proof.
  intros i m t Hmt Him.
  unfold sub_step.
  rewrite upd_nth_diff_Zlength.
  2: split ; try omega ; rewrite upd_nth_Zlength ; rewrite Z2Nat.id ; try omega.
  2: split ; try omega ; rewrite upd_nth_Zlength ; rewrite Z2Nat.id ; try omega.
  2: intros H ; apply (f_equal Z.of_nat) in H ; rewrite ?Z2Nat.id in H ; omega.
  rewrite upd_nth_same_Zlength ; try reflexivity.
  rewrite Z2Nat.id ; try omega.
Qed.

Definition sub_step_1 (a:Z) (m t:list Z) : list Z :=
    let t' := nth (Z.to_nat a) t 0 in
      (upd_nth (Z.to_nat a) m (subst_0xffff t')).

Definition sub_step_2 (a:Z) (m:list Z) : list Z :=
    let m' := nth (Z.to_nat (a - 1)) m 0 in
    let t' := nth (Z.to_nat a) m 0 in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (subst_c t' m')) (mod0xffff m').

Lemma subst_step_1_2 : forall a m t,
  0 < a < Zlength m ->
  sub_step a m t = sub_step_2 a (sub_step_1 a m t).
Proof.
  intros.
  unfold sub_step, sub_step_1, sub_step_2, subst_0xffff, mod0xffff, subst_0xffffc.
  rewrite ?upd_nth_same_Zlength.
  rewrite ?upd_nth_diff_Zlength.
  f_equal.
  rewrite upd_nth_upd_nth_Zlength.
  reflexivity.
  all: try (rewrite Z2Nat.id ; omega).
  clear t.
  intro Ha.
  apply (f_equal Z.of_nat) in Ha.
  rewrite ?Z2Nat.id in Ha ; omega.
Qed.

(* Definition of the for loop : 1 -> 15 *)
Function sub_fn_rev {A} (f:Z -> list A -> list A -> list A) (a:Z) (m t: list A) {measure Z.to_nat a} : (list A) :=
  if (a <=? 1)
    then m
    else
      let prev := sub_fn_rev f (a - 1) m t in 
        f (a - 1) prev t.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Arguments sub_fn_rev [_] _ _ _.

Lemma sub_fn_rev_1 : forall A f (m t:list A),
  sub_fn_rev f 1 m t = m.
Proof. intros. reflexivity. Qed.

Lemma sub_fn_rev_n : forall A f (m t:list A) a,
  1 < a ->
  sub_fn_rev f a m t = f (a - 1) (sub_fn_rev f (a - 1) m t) t.
Proof. intros. rewrite sub_fn_rev_equation.
destruct (a <=? 1) eqn:Eq.
apply Zle_bool_imp_le in Eq; omega.
reflexivity.
Qed.

(* Definition of the for loop : 1 -> 15 *)
Function sub_fn_rev_s {A} (f:Z -> list A -> list A) (a:Z) (m: list A) {measure Z.to_nat a} : (list A) :=
  if (a <=? 1)
    then m
    else
      let prev := sub_fn_rev_s f (a - 1) m in 
        f (a - 1) prev.
Proof. intros. apply Z2Nat.inj_lt ; rewrite Z.leb_gt in teq; omega. Defined.

Arguments sub_fn_rev_s [_] _ _ _.

Lemma sub_fn_rev_s_1 : forall A f (m: list A),
  sub_fn_rev_s f 1 m = m.
Proof. intros. reflexivity. Qed.

Lemma sub_fn_rev_s_n : forall A a (m: list A) f,
  1 < a ->
  sub_fn_rev_s f a m = f (a - 1) (sub_fn_rev_s f (a - 1) m).
Proof. intros. rewrite sub_fn_rev_s_equation.
destruct (a <=? 1) eqn:Eq.
apply Zle_bool_imp_le in Eq; omega.
reflexivity.
Qed.

(*****************************************************************************************
 *   DEFINE SEMANTIC
 *)

Inductive red_expr :=
  | R_red : term -> red_expr
  | Sub_red : red_expr -> red_expr
  | SubC_red : red_expr -> red_expr -> red_expr
  | Mod_red : red_expr -> red_expr.

Inductive formula_red_expr := 
  | Eq_red : list red_expr -> list red_expr -> formula_red_expr.

Fixpoint red_expr_denote env (m : red_expr) : Z :=
  match m with
  | R_red  v  => term_denote env v
  | Sub_red x => subst_0xffff (red_expr_denote env x)
  | SubC_red x y => subst_c (red_expr_denote env x) (red_expr_denote env y)
  | Mod_red x => mod0xffff (red_expr_denote env x)
  end.

Fixpoint red_expr_list_denote env (m: list red_expr) : list Z :=
  match m with
  | nil => nil
  | h :: q => (red_expr_denote env h) :: red_expr_list_denote env q
  end.

Lemma red_expr_list_denote_nth :
  forall i env l, red_expr_denote env (nth i l (R_red (Val 0))) = nth i (red_expr_list_denote env l) 0.
Proof.
intros i env l. gen i. induction l as [|h l IHl] ; intros [|i] ; try reflexivity.
simpl. apply IHl.
Qed.

Lemma red_expr_list_denote_upd_nth :
  forall i env l v, red_expr_list_denote env (upd_nth i l v) = upd_nth i (red_expr_list_denote env l) (red_expr_denote env v).
Proof.
intros i env m. gen i. induction m as [|h m IHm] ; intros [|i] v ; try reflexivity.
simpl. f_equal. apply IHm.
Qed.

Definition formula_red_expr_denote env (t : formula_red_expr) : Prop :=
  match t with
  | Eq_red x y     => red_expr_list_denote env x = red_expr_list_denote env y
  end.

(*****************************************************************************************
 *   DECIDE EQUALITY
 *)

Fixpoint decide_red_expr_eq (l1 l2:red_expr) := match l1, l2 with
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

Lemma decide_red_expr_eq_impl:
  forall env l l', 
  decide_red_expr_eq l l' = true ->
  red_expr_denote env l = red_expr_denote env l'.
Proof.
intros env.
induction l; intros [] H ; simpl in * ;
repeat match goal with
  | _ => discriminate
  | _ => reflexivity
  | [ H : _ && _ = true |- _ ] => apply andb_prop in H; destruct H
  | [ H : term_eqb _ _ = true |- _ ] => apply term_eqb_refl in H; subst
  | [ H : _ = _ |- _ ] => rewrite H
  | [ H : _ , H1 : _ |- _ ] => apply H in H1 (* why bother ? :D *)
end.
Qed.

Lemma decide_red_expr_list_eq_impl:
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
Qed.

Definition decide_formula_red_expr (f : formula_red_expr) : bool := match f with
  | Eq_red x y => decide_red_expr_list_eq x y
  end.

Lemma decide_formula_red_impl : forall env f, decide_formula_red_expr f = true -> formula_red_expr_denote env f.
Proof. intros env [? ?]. by apply decide_red_expr_list_eq_impl. Qed.

(* Weaponize our expression so we can translate functions *)

Definition sub_red_step (a:Z) (m t:list red_expr) : list red_expr :=
    let m' := nth (Z.to_nat (a - 1)) m (R_red (Val 0)) in
    let t' := nth (Z.to_nat a) t (R_red (Val 0)) in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (SubC_red (Sub_red t') m')) (Mod_red m').

Definition sub_red_step_1 (a:Z) (m t:list red_expr) : list red_expr :=
    let t' := nth (Z.to_nat a) t (R_red (Val 0)) in
      (upd_nth (Z.to_nat a) m (Sub_red t')).

Definition sub_red_step_2 (a:Z) (m:list red_expr) : list red_expr :=
    let m' := nth (Z.to_nat (a - 1)) m (R_red (Val 0)) in
    let t' := nth (Z.to_nat a) m (R_red (Val 0)) in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (SubC_red t' m')) (Mod_red m').

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
assert(Hi:= Pos2Z.is_nonneg p).
remember (Z.pos p) as i.
clears p.
gen m t.
apply (natlike_ind (fun i => ∀ m t : list red_expr,
sub_fn_rev sub_step_1 i (red_expr_list_denote env m) (red_expr_list_denote env t) =
red_expr_list_denote env (sub_fn_rev sub_red_step_1 i m t))) ; try omega.
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
  | sub_fn_rev_s _ ?a ?X =>
    allVars_red xs X
  | sub_fn_rev _ ?a ?X ?Y =>
    let xs := allVars_red xs X in
    allVars_red xs Y
  | ?X :: ?Y =>
(*     idtac X; *)
    let xs := allVar xs X in
    allVars_red xs Y
  | _ => 
  xs
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
  | ?X :: ?Y =>
    let x := reifyValue_red env X in
    let y := reifyExpr_red env Y in
    constr:((R_red x) :: y)
  | nil => constr:(nil:list red_expr)
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