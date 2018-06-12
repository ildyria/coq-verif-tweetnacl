From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Export AMZubSqSel.

Open Scope Z.

Class Ops_List `{@Ops (list Z) (list Z) id} :=
{
  A_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (A a b) = 16;
  M_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (M a b) = 16;
  Zub_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (Zub a b) = 16;
  Sq_Zlength : forall a, Zlength a = 16 -> Zlength (Sq a) = 16;
  Sel25519_Zlength : forall b p q, Zlength p = 16 -> Zlength q = 16 -> Zlength (Sel25519 b p q) = 16;
  C_121665_Zlength : Zlength C_121665 = 16;
  C_0_Zlength : Zlength C_0 = 16;
  C_1_Zlength : Zlength C_1 = 16;

  M_bound_Zlength : forall a b,
    Zlength a = 16 ->
    Zlength b = 16 ->
    Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
    Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b);
  Sq_bound_Zlength : forall a,
    Zlength a = 16 ->
    Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Sq a);
  A_bound_Zlength_le : forall m1 n1 m2 n2 a b,
    Zlength a = Zlength b ->
    Forall (fun x => m1 <= x <= n1) a ->
    Forall (fun x => m2 <= x <= n2) b ->
    Forall (fun x => m1 + m2 <= x <= n1 + n2) (A a b);
  A_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
    Zlength a = Zlength b ->
    Forall (fun x => m1 < x < n1) a ->
    Forall (fun x => m2 < x < n2) b ->
    Forall (fun x => m1 + m2 < x < n1 + n2) (A a b);
  Zub_bound_Zlength_le : forall m1 n1 m2 n2 a b,
    Zlength a = Zlength b ->
    Forall (fun x => m1 <= x <= n1) a ->
    Forall (fun x => m2 <= x <= n2) b ->
    Forall (fun x => m1 - n2 <= x <= n1 - m2) (Zub a b);
  Zub_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
    Zlength a = Zlength b ->
    Forall (fun x => m1 < x < n1) a ->
    Forall (fun x => m2 < x < n2) b ->
    Forall (fun x => m1 - n2 < x < n1 - m2) (Zub a b);
  Sel25519_bound_le : forall p pmin pmax q qmin qmax,
    Forall (fun x => pmin <= x <= pmax) p ->
    Forall (fun x => qmin <= x <= qmax) q -> forall b,
    Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q);
  Sel25519_bound_lt_trans_le : forall p pmin pmax q qmin qmax,
    Forall (fun x => pmin < x < pmax) p ->
    Forall (fun x => qmin < x < qmax) q -> forall b,
    Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q);
  Sel25519_bound_lt : forall p pmin pmax q qmin qmax,
    Forall (fun x => pmin < x < pmax) p ->
    Forall (fun x => qmin < x < qmax) q -> forall b,
    Forall (fun x => Z.min pmin qmin < x < Z.max pmax qmax) (Sel25519 b p q);
  Sel25519_bound_lt_le_id : forall pmin pmax p q,
    Forall (fun x => pmin <= x < pmax) p ->
    Forall (fun x => pmin <= x < pmax) q -> forall b,
    Forall (fun x => pmin <= x < pmax) (Sel25519 b p q);
  Sel25519_bound_lt_lt_id : forall pmin pmax p q,
    Forall (fun x => pmin < x < pmax) p ->
    Forall (fun x => pmin < x < pmax) q -> forall b,
    Forall (fun x => pmin < x < pmax) (Sel25519 b p q);
  Sel25519_bound_le_le_id : forall pmin pmax p q,
    Forall (fun x => pmin <= x <= pmax) p ->
    Forall (fun x => pmin <= x <= pmax) q -> forall b,
    Forall (fun x => pmin <= x <= pmax) (Sel25519 b p q);
  Sel25519_bound_le_lt_trans_le_id : forall pmin pmax p q,
    Forall (fun x => pmin <= x < pmax) p ->
    Forall (fun x => pmin <= x < pmax) q -> forall b,
    Forall (fun x => pmin <= x <= pmax) (Sel25519 b p q);
  C_121665_bound : Forall (fun x => 0 <= x < 2 ^16) C_121665;
  C_0_bound : Forall (fun x => 0 <= x < 2 ^16) C_0;
  C_1_bound : Forall (fun x => 0 <= x < 2 ^16) C_1
  }.

Close Scope Z.