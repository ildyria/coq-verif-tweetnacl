Require Import ssreflect.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.

Section Montgomery_Rec.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Open Scope Z.

Local Notation "X + Y" := (A X Y) (only parsing).
Local Notation "X - Y" := (Zub X Y) (only parsing).
Local Notation "X * Y" := (M X Y) (only parsing).
Local Notation "X ^2" := (Sq X) (at level 40,
  only parsing, left associativity).

Fixpoint montgomery_rec_swap (m : nat) (z : T')
(a: T) (b: T) (c: T) (d: T) (e: T) (f: T) (x: T) (swap:Z):
(* a: x2              *)
(* b: x3              *)
(* c: z2              *)
(* d: z3              *)
(* e: temporary  var  *)
(* f: temporary  var  *)
(* x: x1              *)
(T * T * T * T * T * T) :=
match m with
| 0%nat => 
  let (a, b) := (Sel25519 swap a b, Sel25519 swap b a) in
    (* (x_2, x_3) = cswap(swap, x_2, x_3)            *)
  let (c, d) := (Sel25519 swap c d, Sel25519 swap d c) in
    (* (z_2, z_3) = cswap(swap, z_2, z_3)            *)
  (a,b,c,d,e,f)
| S n =>
  let r := Getbit (Z.of_nat n) z in
    (* k_t = (k >> t) & 1                            *)
    (* swap <- k_t                                   *)
  let swap := Z.lxor swap r in
  let (a, b) := (Sel25519 swap a b, Sel25519 swap b a) in
    (* (x_2, x_3) = cswap(swap, x_2, x_3)            *)
  let (c, d) := (Sel25519 swap c d, Sel25519 swap d c) in
    (* (z_2, z_3) = cswap(swap, z_2, z_3)            *)
  let e := a + c in   (* A = x_2 + z_2               *)
  let a := a - c in   (* B = x_2 - z_2               *)
  let c := b + d in   (* C = x_3 + z_3               *)
  let b := b - d in   (* D = x_3 - z_3               *)
  let d := e ^2 in    (* AA = A^2                    *)
  let f := a ^2 in    (* BB = B^2                    *)
  let a := c * a in   (* CB = C * B                  *)
  let c := b * e in   (* DA = D * A                  *)
  let e := a + c in   (* x_3 = (DA + CB)^2           *)
  let a := a - c in   (* z_3 = x_1 * (DA - CB)^2     *)
  let b := a ^2 in    (* z_3 = x_1 * (DA - CB)^2     *)
  let c := d - f in   (* E = AA - BB                 *)
  let a := c * C_121665 in
                      (* z_2 = E * (AA + a24 * E)    *)
  let a := a + d in   (* z_2 = E * (AA + a24 * E)    *)
  let c := c * a in   (* z_2 = E * (AA + a24 * E)    *)
  let a := d * f in   (* x_2 = AA * BB               *)
  let d := b * x in   (* z_3 = x_1 * (DA - CB)^2     *)
  let b := e ^2 in    (* x_3 = (DA + CB)^2           *)
(*   let (a, b) := (Sel25519 r a b, Sel25519 r b a) in *)
    (* (x_2, x_3) = cswap(swap, x_2, x_3)            *)
(*   let (c, d) := (Sel25519 r c d, Sel25519 r d c) in *)
    (* (z_2, z_3) = cswap(swap, z_2, z_3)            *)
  montgomery_rec_swap n z a b c d e f x r
end.

Close Scope Z.

End Montgomery_Rec.