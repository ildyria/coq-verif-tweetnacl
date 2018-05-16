Require Import Tweetnacl.Libs.Export.
Require Import ssreflect.

Section ScalarRec.
Open Scope Z.

Variable A : Z -> Z -> Z.
Variable M : Z -> Z -> Z.
Variable Zub : Z -> Z -> Z.
Variable Sq : Z -> Z.
Variable _121665: Z.
Variable Sel25519 : Z -> Z -> Z -> Z.
Variable getbit : Z -> Z -> Z.

Definition fa r (a b c d e f x:Z) :=
  Sel25519 r
     (M (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (Sq
        (A
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))).

Definition fb r (a b c d e f x:Z) :=
  Sel25519 r
     (Sq
        (A
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d)))))
     (M (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))).

Definition fc r (a b c d e f x:Z) :=
Sel25519 r
  (M
     (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (A
        (M
           (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
              (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))) _121665)
        (Sq (A (Sel25519 r a b) (Sel25519 r c d)))))
  (M
     (Sq
        (Zub
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))) x).

Definition fd r (a b c d e f x:Z) :=
Sel25519 r
  (M
     (Sq
        (Zub
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))) x)
  (M
     (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (A
        (M
           (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
              (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))) _121665)
        (Sq (A (Sel25519 r a b) (Sel25519 r c d))))).

Definition fe r (a b c d e f x:Z) :=
A
  (M (A (Sel25519 r b a) (Sel25519 r d c))
     (Zub (Sel25519 r a b) (Sel25519 r c d)))
  (M (Zub (Sel25519 r b a) (Sel25519 r d c))
     (A (Sel25519 r a b) (Sel25519 r c d))).

Definition ff r (a b c d e f x:Z) :=
  Sq (Zub (Sel25519 r a b) (Sel25519 r c d)).

Variable M_bound_Zlength : forall a b,
  (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Variable Sq_bound_Zlength : forall a,
  (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  (fun x => -38 <= x < Z.pow 2 16 + 38) (Sq a).
(* Variable A_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  (fun x => m1 <= x <= n1) a -> 
  (fun x => m2 <= x <= n2) b -> 
  (fun x => m1 + m2 <= x <= n1 + n2) (A a b). *)
Variable A_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  (fun x => m1 < x < n1) a -> 
  (fun x => m2 < x < n2) b -> 
  (fun x => m1 + m2 < x < n1 + n2) (A a b).
(* Variable Zub_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  (fun x => m1 <= x <= n1) a -> 
  (fun x => m2 <= x <= n2) b -> 
  (fun x => m1 - n2 <= x <= n1 - m2) (Zub a b). *)
Variable Zub_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  (fun x => m1 < x < n1) a -> 
  (fun x => m2 < x < n2) b -> 
  (fun x => m1 - n2 < x < n1 - m2) (Zub a b).
Variable Sel25519_bound_le : forall p pmin pmax q qmin qmax,
  (fun x => pmin <= x <= pmax) p ->
  (fun x => qmin <= x <= qmax) q -> forall b,
  (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q).
Variable Sel25519_bound_lt_le_id : forall pmin pmax p q,
  (fun x => pmin <= x < pmax) p ->
  (fun x => pmin <= x < pmax) q -> forall b,
  (fun x => pmin <= x < pmax) (Sel25519 b p q).
Variable Sel25519_bound_lt_lt_id : forall pmin pmax p q,
  (fun x => pmin < x < pmax) p ->
  (fun x => pmin < x < pmax) q -> forall b,
  (fun x => pmin < x < pmax) (Sel25519 b p q).
Variable Sel25519_bound_le_lt_trans_le_id : forall pmin pmax p q,
  (fun x => pmin <= x < pmax) p ->
  (fun x => pmin <= x < pmax) q -> forall b,
  (fun x => pmin <= x <= pmax) (Sel25519 b p q).
Variable _121665_bound : (fun x => 0 <= x < 2 ^16) _121665.

Local Ltac Simplify_this :=
change (2^16) with 65536 in *;
change (2^26) with 67108864 in *.

Local Ltac solve_Sel25519 :=
  match goal with 
    | [ |- context[Sel25519] ] => apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)) ; omega
    | _ => Simplify_this ; omega
  end.

Lemma fa_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => -38 <= x < 2^16 + 38) (fa r a b c d e f x).
Proof.
  intros r a b c d e f x Ha Hb Hc Hd ; simpl in *.
  apply Sel25519_bound_lt_le_id.
  {
  apply M_bound_Zlength.
  1,2: eapply bounds.lelt_lt_trans.
  1,4: apply Sq_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  apply A_bound_Zlength_lt.
  5: apply Zub_bound_Zlength_lt.
  all: solve_Sel25519.
  }
  apply Sq_bound_Zlength.
  eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply M_bound_Zlength.
  1,2,3,4: eapply bounds.lt_lt_trans.
  1,10: apply A_bound_Zlength_lt.
  7,10: apply Zub_bound_Zlength_lt.
  all: solve_Sel25519.
Qed.

Lemma fb_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => -38 <= x < 2^16 + 38) (fb r a b c d e f x).
Proof.
  intros r a b c d e f x Ha Hb Hc Hd ; simpl in *.
  apply Sel25519_bound_lt_le_id.
  {
  apply Sq_bound_Zlength.
  eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply M_bound_Zlength.
  1,2,3,4: eapply bounds.lt_lt_trans.
  1,10: apply A_bound_Zlength_lt.
  7,10: apply Zub_bound_Zlength_lt.
  all: solve_Sel25519.
  }
  eapply M_bound_Zlength.
  1,2: eapply bounds.lelt_lt_trans.
  1,4: apply Sq_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  5: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: solve_Sel25519.
Qed.


Lemma fc_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (fc r a b c d e f x).
Proof.
  intros r a b c d e f x Ha Hb Hc Hd Hx; simpl in *.
  apply Sel25519_bound_lt_le_id.
  1,2: apply M_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  {
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply Sq_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  5: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: solve_Sel25519.
  }
  1,2: solve_Sel25519.
  {
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  3: apply Sq_bound_Zlength.
  3: eapply bounds.lt_lt_trans.
  3: apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  apply M_bound_Zlength.
  eapply bounds.lt_lt_trans.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply Sq_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  5: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: solve_Sel25519.
  }
  1,2: solve_Sel25519.
  eapply bounds.lelt_lt_trans.
  apply Sq_bound_Zlength.
  eapply bounds.lt_lt_trans.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply M_bound_Zlength.
  1,2,3,4: eapply bounds.lt_lt_trans.
  1,10: apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  7,10: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: try solve_Sel25519.
Qed.

Lemma fd_bound : forall r a b c d e f x,
    (fun x => -38 <= x < 2^16 + 38) a ->
    (fun x => -38 <= x < 2^16 + 38) b ->
    (fun x => -38 <= x < 2^16 + 38) c ->
    (fun x => -38 <= x < 2^16 + 38) d ->
    (fun x => 0 <= x < 2^16) x ->
    (fun x => -38 <= x < 2^16 + 38) (fd r a b c d e f x).
Proof.
  intros r a b c d e f x Ha Hb Hc Hd Hx; simpl in *.
  apply Sel25519_bound_lt_le_id.
  1,2: apply M_bound_Zlength.
  {
  eapply bounds.lelt_lt_trans.
  apply Sq_bound_Zlength.
  eapply bounds.lt_lt_trans.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply M_bound_Zlength.
  1,2,3,4: eapply bounds.lt_lt_trans.
  1,10: apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  7,10: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: try solve_Sel25519.
  }
  solve_Sel25519.
  {
  eapply bounds.lt_lt_trans.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply Sq_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  5: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: solve_Sel25519.
  }
  eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  3: apply Sq_bound_Zlength.
  3: eapply bounds.lt_lt_trans.
  3: apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  apply M_bound_Zlength.
  eapply bounds.lt_lt_trans.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  1,2: eapply bounds.lelteq_lt_trans.
  1,3: apply Sq_bound_Zlength.
  1,2: eapply bounds.lt_lt_trans.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  5: apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  all: solve_Sel25519.
Qed.

End ScalarRec.

Close Scope Z.