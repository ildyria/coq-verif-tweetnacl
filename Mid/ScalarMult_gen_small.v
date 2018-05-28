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

End ScalarRec.

Close Scope Z.