From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.

Class Ops_Mod_P {T} {U} `{Ops T} `{Ops U} :=
{

P : T -> U;
Mod :U -> U;
A_eq : forall a b, Mod (P (A a b)) = Mod (A (P a) (P b));
M_eq : forall a b, Mod (P (M a b)) = Mod (M (P a) (P b));
Zub_eq : forall a b,  Mod (P (Zub a b)) = Mod (Zub (P a) (P b));
Sq_eq : forall a,  Mod (P (Sq a)) = Mod (Sq (P a));
_121665_eq : Mod (P _121665) = Mod (_121665);
Sel25519_eq : forall b p q,  Mod (P (Sel25519 b p q)) = Mod (Sel25519 b (P p) (P q));
getbit_eq : forall i p,  getbit i p = getbit i (P p);

Mod_ZSel25519_eq : forall b p q,  Mod (Sel25519 b p q) = Sel25519 b (Mod p) (Mod q);
Mod_ZA_eq : forall p q,  Mod (A p q) = Mod (A (Mod p) (Mod q));
Mod_ZM_eq : forall p q,  Mod (M p q) = Mod (M (Mod p) (Mod q));
Mod_ZZub_eq : forall p q,  Mod (Zub p q) = Mod (Zub (Mod p) (Mod q));
Mod_ZSq_eq : forall p,  Mod (Sq p) = Mod (Sq (Mod p));
Mod_red : forall p,  Mod (Mod p) = (Mod p)
}.
