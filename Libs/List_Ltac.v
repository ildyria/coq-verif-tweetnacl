Set Warnings "-notation-overridden".
Require Import Tweetnacl.Libs.List_Decidable.
(**************************************************************************
 * Data type for representing partial results, taken from Chlipala's CPDT
 *)

Inductive partial (P : Prop) : Set :=
| Proved : P -> partial P
| Uncertain : partial P.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _ _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) (at level 100) : partial_scope.

(* Open Scope Z. *)


(**************************************************************************
 * Environment management tactics
 *)

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(1%positive)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
  end.

Ltac allVar xs e :=
  match e with
  | Z0 => xs
  | Zpos _ => xs
  | Zneg _ => xs
  | _ => addToList e xs
  end.

Ltac allVars xs e :=
  match e with
  | Z.mul ?X ?Y =>
    let xs := allVars xs X in
    allVars xs Y
  | Z.add ?X ?Y =>
    let xs := allVars xs X in
    allVars xs Y
  | nil => xs
  | ?hp :: ?qp => 
    let xs1 := allVars xs hp in
    allVars xs1 qp
  | ?P = ?Q =>
    let xs := allVars xs P in
    allVars xs Q
  | ?X => allVar xs X
  | _ => xs
  end.

(**************************************************************************
 * Reflection tactics
 *)

Ltac reifyValue env t :=
  match t with
  | ?X =>
    let v := lookup X env in
    constr:(Var v)
  | _ => constr:(Val t)
(*   | Zneg _ =>
    constr:(Val t)
  | Zpos _ =>
    constr:(Val t) *)
  end.

Ltac reifyExpr env t :=
  lazymatch t with
  | Z.mul ?X ?Y =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    constr:(M x y)
  | ?X * ?Y =>
    let x := reifyValue env X in
    let y := reifyValue env Y in
    constr:(M x y)
  | Z.add ?X ?Y =>
    let x := reifyExpr env X in
    let y := reifyExpr env Y in
    constr:(A x y)
  | ?X + ?Y =>
    let x := reifyExpr env X in
    let y := reifyExpr env Y in
    constr:(A x y)
  | ?X =>
    let x := reifyValue env X in
    constr:(R x)
  end.

Ltac reifyList env t :=
  match t with
  | nil => constr:(nil:list expr)
  | cons ?X ?Y =>
    let x := reifyExpr env X in
    let y := reifyList env Y in
    constr:(x :: y)
  end.

Ltac reifyTerm env t :=
  lazymatch t with
  | cons ?X ?X' = cons ?Y ?Y' => 
      let x := reifyList env (cons X X') in
      let y := reifyList env (cons Y Y') in
      constr:(LEq x y)
   | ?X = ?Y =>
      let x := reifyExpr env X in
      let y := reifyExpr env Y in
      constr:(Eq x y)
  end.

Ltac gather_vars :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    pose xs
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

Local Ltac reify_debug :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    pose xs;
    pose env;
    pose r1
  end.

Ltac reify :=
  match goal with
  | [ |- ?X ] =>
    let xs  := allVars tt X in
    let env := functionalize xs in
    let r1  := reifyTerm xs X in
    change (formula_denote {| vars := env |} r1)
  end.


(**************************************************************************
 * User interface tactics
 *)

Ltac mini_ring := intros; reify; apply decide_formula_impl; vm_compute; auto.

Open Scope Z.
Local Example example1 : forall x y, x * y = y * x.
Proof. intros ; reify; apply decide_formula_impl; vm_compute; auto. Qed.

Local Example example2 : forall x y z, x*y :: z :: nil = y * x :: z :: nil.
Proof. mini_ring. Qed.

Local Example example3 : forall x, (2*3*4*x = 3*4*2*x)%Z.
Proof. mini_ring. Qed.

