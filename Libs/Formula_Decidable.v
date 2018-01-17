Require Import Tweetnacl.Libs.Decidable.

Section formula_denote.

Context {T} {U} (inst : @Decidable T U).

Inductive formula :=
  | Eq : T -> T -> formula.

Definition formula_denote env (t : formula) : Prop :=
  match t with
  | Eq x y     => denote env x = denote env y
  end.

Definition formula_decide (f : formula) : bool := match f with
  | Eq x y => decide x y
  end.

Lemma formula_decide_impl : forall env f, formula_decide f = true -> formula_denote env f.
Proof. intros env [? ?]. apply decide_impl. Qed.

End formula_denote.

(* we can't make a Instance of that function because the signature is different *)