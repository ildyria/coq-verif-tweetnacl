From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.

Section ScalarRec.

Context {T : Type}.
Context {T' : Type}.
Context {Mod : T -> T}.
Context {O : Ops T T' Mod}.

Definition step_gen (z:T') (x:T) (n:nat) (k:(T * T * T * T * T * T)) : (T * T * T * T * T * T)
  := match k with (a,b,c,d,e,f) =>
      let r := Getbit (Z.of_nat n) z in
      (Gen.fa r a b c d e f x,
       Gen.fb r a b c d e f x,
       Gen.fc r a b c d e f x,
       Gen.fd r a b c d e f x,
       Gen.fe r a b c d e f x,
       Gen.ff r a b c d e f x)
      end.

End ScalarRec.