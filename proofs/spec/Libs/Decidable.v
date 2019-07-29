Require Export Coq.ZArith.ZArith.

Record environment := { vars : positive -> Z }.

Open Scope Z_scope.

Class Decidable {T U: Type} :=
  {
    decide : T -> T -> bool;
    denote : environment -> T -> U;
    decide_impl: forall (env:environment) (a b :T),
      decide a b = true -> denote env a = denote env b
  }.

Close Scope Z.