Require Import ZArith.
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From Tweetnacl.Gen Require Export AMZubSqSel.
Open Scope Z.

Class Ops_Prop_List_Z (Mod : Z -> Z) `{@Ops (list Z) (list Z) id} `{@Ops Z Z Mod}  :=
{
  A_correct:
    forall n a b,
      ZofList n (A a b) = A (ZofList n a) (ZofList n b);
  mult_GF_Zlengh :
    forall a b,
    Zlength a = 16 ->
    Zlength b = 16 ->
    Mod (ℤ16.lst M a b) = Mod (M (ℤ16.lst a) (ℤ16.lst b));
  Zub_correct :
    forall n a b,
      ZofList n (Zub a b) = Zub (ZofList n a) (ZofList n b);
  Sq_GF_Zlengh :
    forall a,
    Zlength a = 16 ->
    Mod (ℤ16.lst Sq a) = Mod (Sq (ℤ16.lst a) );
  C_121665_correct :
    ℤ16.lst C_121665 = C_121665;
  C_1_correct :
    ℤ16.lst C_1 = C_1;
  C_0_correct :
    ℤ16.lst C_0 = C_0;
  Sel25519_correct:
    forall b p q,
    ℤ16.lst Sel25519 b p q = Sel25519 b (ℤ16.lst p) (ℤ16.lst q);
  GetBit_correct:
    forall b p,
    Forall (fun x => 0 <= x < 2^8) p ->
    Getbit b (ZofList 8 p) = Getbit b p
}.

Close Scope Z.

