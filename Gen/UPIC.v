Class Ops_ext (T T': Type) :=
{
  Unpack25519 : T' -> T;
  Pack25519 : T -> T';
  Inv25519 : T -> T;
  Clamp : T' -> T';

(*   Mod_Inv25519_eq : forall p,  Mod (Inv25519 p) = Inv25519 (Mod p); *)
(*   Mod_Pack25519_eq : forall p,  Pack25519 p = Mod p; *)
}.

