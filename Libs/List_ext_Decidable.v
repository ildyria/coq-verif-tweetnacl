Set Warnings "-notation-overridden".
Require Export Coq.ZArith.ZArith.
Require Export Coq.Lists.List.
Require Import Tweetnacl.Libs.Decidable.
Require Import Tweetnacl.Libs.Expr_Decidable.
Require Import Tweetnacl.Libs.Term_Decidable.
Require Import Tweetnacl.Libs.List_Decidable.
Require Import Tweetnacl.Libs.Lists_extended.
Require Import ssreflect.

Open Scope Z_scope.

Section list_upd_denote.

Context {T} {U} (inst : @Decidable T U).
Instance  list_dec : Decidable := 
{
  decide := list_decide inst;
  denote := list_denote inst;
  decide_impl := list_decide_impl inst
}.

Inductive list_upd_ext :=
  | List  : list T -> list_upd_ext
  | Upd   : nat -> list_upd_ext -> T -> list_upd_ext.

Fixpoint list_upd_ext_denote (env:environment) (l:list_upd_ext) : list U := match l with
  | List l'    => denote env l'
  | Upd n l' v => upd_nth n (list_upd_ext_denote env l') (denote env v)
end.

Local Lemma upd_nth_denote : forall (env:environment) n l v,
  upd_nth n (list_denote inst env l) (denote env v) = denote env (upd_nth n l v).
Proof.
induction n as [|n IHn] ; destruct l as [|h l] => v //.
simpl. rewrite IHn.
reflexivity.
Qed.

Local Lemma upd_nth_list_upd_ext_denote : forall (env:environment) n l v,
  upd_nth n (list_upd_ext_denote env l) (denote env v) = list_upd_ext_denote env (Upd n l v).
Proof. reflexivity. Qed.

Fixpoint SomeList (n:nat) (m:list_upd_ext) (v:T) : list T := match m with
  | List l => upd_nth n l v
  | Upd n' l' v' => upd_nth n (SomeList n' l' v') v
end.

Local Lemma SomeListDenote : forall (env:environment) (n:nat) (l:list_upd_ext) (v:T),
  list_upd_ext_denote env (Upd n l v) = list_upd_ext_denote env (List (SomeList n l v)).
Proof.
  intros env.
  fix 2.
  intros n l v.
  destruct l ; simpl; change (list_denote _ ?A ?B) with (denote A B);
  rewrite -upd_nth_denote ;  try reflexivity.
  specialize SomeListDenote with n0 l t;
  simpl in SomeListDenote;
  rewrite SomeListDenote;
  reflexivity.
Qed.

Definition list_upd_ext_decide (l l':list_upd_ext) : bool := match l with
  | List m         =>
    match l' with
      | List m'    => decide m m'
      | Upd n' m' v' => decide m (SomeList n' m' v')
    end
  | Upd n m v     => 
    match l' with
      | List m' => decide (SomeList n m v) m'
      | Upd n' m' v' => decide (SomeList n m v) (SomeList n' m' v')
    end
  end.

Lemma list_upd_ext_decide_impl : forall (env:environment) (l l' : list_upd_ext),
  list_upd_ext_decide l l' = true -> list_upd_ext_denote env l = list_upd_ext_denote env l'.
Proof.
  intros env; induction l as [|n l Hl];
  destruct l' => Hll' ; simpl in *; apply (list_decide_impl inst env) in Hll';
  repeat change (list_denote inst env ?A) with (list_upd_ext_denote env (List A)) in Hll';
  change (list_denote inst env ?A) with (list_upd_ext_denote env (List A));
  rewrite -?SomeListDenote in Hll';
  assumption.
Qed.

End list_upd_denote.

(* Section list_nth_denote.
Context {T} {U} (inst : @Decidable T U).
Instance  list_dec2 : Decidable := 
{
  decide := list_decide inst;
  denote := list_denote inst;
  decide_impl := list_decide_impl inst
}.

Inductive list_nth_ext :=
  | Nv  : T -> list_nth_ext
  | Nth : nat -> list T -> T -> list_nth_ext.

Definition list_nth_ext_denote (env:environment) (l:list_nth_ext) : U := match l with
  | Nv  v    => denote env v
  | Nth n l' v => nth n (denote env l') (denote env v)
end.

Local Lemma nth_denote : forall (env:environment) n l v,
  nth n (list_denote inst env l) (denote env v) = denote env (nth n l v).
Proof.
induction n as [|n IHn] ; destruct l as [|h l] => v //.
simpl. rewrite IHn.
reflexivity.
Qed.

Definition list_nth_ext_decide (l l':list_nth_ext) : bool := match l with
  | Nv m         =>
    match l' with
      | Nv m'    => decide m m'
      | Nth n' m' v' => decide m (nth n' m' v')
    end
  | Nth n m v     => 
    match l' with
      | Nv m' => decide (nth n m v) m'
      | Nth n' m' v' => decide (nth n m v) (nth n' m' v')
    end
  end.

Lemma list_nth_ext_decide_impl : forall (env:environment) (l l' : list_nth_ext),
  list_nth_ext_decide l l' = true -> list_nth_ext_denote env l = list_nth_ext_denote env l'.
Proof.
  intros env; induction l as [|n l v];
  destruct l' => Hll' ; simpl in *; rewrite ?nth_denote; by apply decide_impl.
Qed.
End list_nth_denote. *)

Close Scope Z.