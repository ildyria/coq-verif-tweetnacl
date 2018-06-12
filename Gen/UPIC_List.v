(* From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Export UPIC.

Open Scope Z.
Class Ops_ext_List `{@Ops_ext (list Z) (list Z)} :=
{
  Inv25519_Zlength : forall a, Zlength a = 16 -> Zlength (Inv25519 a) = 16;
  Unpack_Zlength : forall a, Zlength a = 32 -> Zlength (Unpack25519 a) = 16;
  Clamp_Zlength : forall a, Zlength a = 32 -> Zlength (Clamp a) = 32;
  Pack_Zlength : forall a, Zlength a = 16 -> Zlength (Pack25519 a) = 32;

  Clamp_bound : forall l,
    Forall (fun x => 0 <= x < Z.pow 2 8) l ->
    Forall (fun x => 0 <= x < Z.pow 2 8) (Clamp l);
  Inv25519_bound: forall g,
    Zlength g = 16 ->
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) g ->
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Inv25519 g);
  Pack25519_bound : forall (l:list Z),
    Zlength l = 16 ->
    Forall (fun x => -2^62 < x < 2^62) l ->
    Forall (fun x => 0 <= x < 2^8) (Pack25519 l)

}.
Close Scope Z. *)