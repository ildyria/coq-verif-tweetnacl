From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.

Section ScalarRec.

Context {T : Type}.
Context {T' : Type}.
Context {O : Ops T T'}.

Definition step_gen (z:T') (x:T) (n:nat) (k:(T * T * T * T * T * T)) : (T * T * T * T * T * T)
  := match k with (a,b,c,d,e,f) =>
      let r := Getbit (Z.of_nat n) z in
      (fa r a b c d e f x,
       fb r a b c d e f x,
       fc r a b c d e f x,
       fd r a b c d e f x,
       fe r a b c d e f x,
       ff r a b c d e f x)
      end.

End ScalarRec.