Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice.
From mathcomp Require Import fintype ssralg finalg.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope ring_scope.
Import GRing.Theory.

Ltac ring_unfold:=
repeat match goal with
  | _ => progress rewrite /GRing.mul
  | _ => progress rewrite /GRing.add
  | _ => progress rewrite /GRing.opp
end; move => /=.

Ltac ring_simplify_this :=
  repeat match goal with
  | _ => rewrite GRing.expr0
  | _ => rewrite GRing.exprS
  | _ => rewrite GRing.mul1r
  | _ => rewrite GRing.mulr1
  | _ => rewrite GRing.mul0r
  | _ => rewrite GRing.mulr0
  | _ => rewrite GRing.mulr0n
  | _ => rewrite GRing.add0r
  | _ => rewrite GRing.oppr0
  | _ => rewrite GRing.addr0
  | _ => done
end.


Close Scope ring_scope.