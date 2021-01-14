(* Check that extra arguments to Arguments Scope do not disturb use of *)
(* scopes in constructors *)

Inductive stmt : Type := Sskip: stmt | Scall : nat -> stmt.
Bind Scope Cminor with stmt.

(* extra argument is ok because of possible coercion to funclass *)
Arguments Scope Scall [_ Cminor ].

(* extra argument is ok because of possible coercion to funclass *)
Fixpoint f (c: stmt) : Prop := match c with Scall _ => False | _ => False end.
