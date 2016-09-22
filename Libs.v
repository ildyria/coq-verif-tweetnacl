Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Export Coq.Arith.EqNat.
Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Require Export Coq.ZArith.ZArith.
Require Export Coq.Numbers.Natural.Peano.NPeano.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Program.Equality. (**r Necessary for 'dependent induction'. *)

Require Export LibTactics.


Ltac autoinjection :=
  repeat match goal with
           | h: ?f _ = ?f _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ = ?f _  _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ = ?f _ _ _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ _ = ?f _ _ _ _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ _ _ = ?f _ _ _ _ _ |- _ => injection h; intros; clear h; subst
         end.

Ltac go := 
  simpl in *;
  repeat match goal with
           | h: ?x = _ |- context[match ?x with _ => _ end] => rewrite h
         end;
  autoinjection;
  try (congruence); 
  try omega; 
  subst; 
  eauto 4 with zarith datatypes;
  try (econstructor ; (solve[go])).

Tactic Notation "go" := try (go; fail).

Ltac go_with b := 
  simpl in *;
  repeat match goal with
           | h: ?x = _ |- context[match ?x with _ => _ end] => rewrite h
         end;
  autoinjection;
  try (congruence); 
  try omega; 
  subst; 
  eauto 4 with zarith datatypes b;
  try (econstructor ; (solve[go])).

Ltac inv H := inversion H; try subst; clear H.

Tactic Notation "flatten" ident(H) :=
  repeat match goal with
    | H: context[match ?x with | left _ => _ | right _ => _ end] |- _ => destruct x
    | H: context[match ?x with | _ => _ end] |- _ => let E := fresh "Eq" in destruct x eqn:E
  end; autoinjection; try congruence.

Tactic Notation "flatten" :=
  repeat match goal with
    | |- context[match ?x with | left _ => _ | right _ => _ end] => destruct x
    | |- context[match ?x with | _ => _ end] => let E := fresh "Eq" in destruct x eqn:E
  end; autoinjection; try congruence.

(*Tactic Notation "induction" ident(x) := dependent induction x.*)

Definition admit {T: Type} : T.  Admitted.

Tactic Notation "solve_by_inversion_step" tactic(t) :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; t ]
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.
