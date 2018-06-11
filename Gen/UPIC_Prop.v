From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import UPIC.

Class Ops_ext_Mod_P {T T' U:Type} `(Ops U U) `(Ops_ext T T') `(Ops_ext U U) :=
{
P : T -> U;
P' : T' -> U;

Inv25519_eq : forall a, Mod (P (Inv25519 a)) = Mod (Inv25519 (P a));
Inv25519_mod_eq : forall a, Mod (Inv25519 a) = Mod (Inv25519 (Mod a));
Pack25519_eq : forall l, P' (Pack25519 l) = Pack25519 (P l);
Mod_Pack25519_eq : forall p,  Pack25519 p = Mod p;

Unpack25519_eq : forall l, P (Unpack25519 l) = Unpack25519 (P' l);
Clamp_eq : forall l, P' (Clamp l) = Clamp (P' l);


}.