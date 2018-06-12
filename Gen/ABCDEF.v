From Tweetnacl.Gen Require Import AMZubSqSel.

Section ABCDEF.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : @Ops T T' Mod}.

Definition fa r (a b c d e f x:T) :=
  Sel25519 r
     (M (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (Sq
        (A
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))).
Definition fb r (a b c d e f x:T) :=
  Sel25519 r
     (Sq
        (A
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d)))))
     (M (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))).
Definition fc r (a b c d e f x:T) :=
Sel25519 r
  (M
     (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (A
        (M
           (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
              (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))) C_121665)
        (Sq (A (Sel25519 r a b) (Sel25519 r c d)))))
  (M
     (Sq
        (Zub
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))) x).
Definition fd r (a b c d e f x:T) :=
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
              (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))) C_121665)
        (Sq (A (Sel25519 r a b) (Sel25519 r c d))))).
Definition fe r (a b c d e f x:T) :=
A
  (M (A (Sel25519 r b a) (Sel25519 r d c))
     (Zub (Sel25519 r a b) (Sel25519 r c d)))
  (M (Zub (Sel25519 r b a) (Sel25519 r d c))
     (A (Sel25519 r a b) (Sel25519 r c d))).
Definition ff r (a b c d e f x:T) :=
  Sq (Zub (Sel25519 r a b) (Sel25519 r c d)).

End ABCDEF.