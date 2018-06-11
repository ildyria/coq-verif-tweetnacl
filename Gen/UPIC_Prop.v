From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import UPIC.

Class Ops_ext_Mod_P {T T' U:Type} `(Ops U U) `(Ops_ext T T') `(Ops_ext U U) :=
{

P : T -> U;
P' : T' -> U;
Inv25519_eq : forall a, Mod (P (Inv25519 a)) = Mod (Inv25519 (P a));
Pack25519 : forall l, P' (Pack25519 l) = Pack25519 (P l)

}.