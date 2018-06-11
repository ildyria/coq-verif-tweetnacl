Class Ops_ext (T T': Type) :=
{
  Unpack25519 : T' -> T;
  Pack25519 : T -> T';
  Inv25519 : T -> T;
  Clamp : T' -> T';
}.

