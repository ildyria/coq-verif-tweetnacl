From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import UPIC.


Class Ops_Mod_P {T T' U:Type} `(Ops T T') `(Ops U U) :=
{

P : T -> U;
P' : T' -> U;
A_eq : forall a b, Mod (P (A a b)) = Mod (A (P a) (P b));
M_eq : forall a b, Mod (P (M a b)) = Mod (M (P a) (P b));
Zub_eq : forall a b,  Mod (P (Zub a b)) = Mod (Zub (P a) (P b));
Sq_eq : forall a,  Mod (P (Sq a)) = Mod (Sq (P a));
C_121665_eq : P C_121665 = C_121665;
C_0_eq : P C_0 = C_0;
C_1_eq : P C_1 = C_1;
Sel25519_eq : forall b p q,  Mod (P (Sel25519 b p q)) = Mod (Sel25519 b (P p) (P q));
Getbit_eq : forall i p,  Getbit i p = Getbit i (P' p);

}.