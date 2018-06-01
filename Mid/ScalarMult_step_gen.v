Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Section ScalarRec.

Variable Zfa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zfe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable Zgetbit : Z -> Z -> Z.

Definition Zstep_gen (z x:Z) (n:nat) k : (Z * Z * Z * Z * Z * Z)
  := match k with  (a,b,c,d,e,f) =>
      let r := Zgetbit (Z.of_nat n) z in
      (Zfa r a b c d e f x,
        Zfb r a b c d e f x,
        Zfc r a b c d e f x,
        Zfd r a b c d e f x,
        Zfe r a b c d e f x,
        Zff r a b c d e f x)
      end.

End ScalarRec.