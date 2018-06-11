Require Import ZArith.

Open Scope Z.

Class Ops (T T': Type) :=
{
  A : T -> T -> T;
  M : T -> T -> T;
  Zub : T -> T -> T;
  Sq : T -> T;
  C_0 : T;
  C_1 : T;
  C_121665: T;
  Sel25519 : Z -> T -> T -> T;
  Getbit : Z -> T' -> Z;

  Mod : T -> T;

  Mod_ZSel25519_eq : forall b p q,  Mod (Sel25519 b p q) = Sel25519 b (Mod p) (Mod q);
  Mod_ZA_eq : forall p q,  Mod (A p q) = Mod (A (Mod p) (Mod q));
  Mod_ZM_eq : forall p q,  Mod (M p q) = Mod (M (Mod p) (Mod q));
  Mod_ZZub_eq : forall p q,  Mod (Zub p q) = Mod (Zub (Mod p) (Mod q));
  Mod_ZSq_eq : forall p,  Mod (Sq p) = Mod (Sq (Mod p));
  Mod_red : forall p,  Mod (Mod p) = (Mod p)
}.

Close Scope Z.

