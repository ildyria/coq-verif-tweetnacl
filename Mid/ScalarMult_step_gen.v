Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Section ScalarRec.

Variable fa : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fb : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fc : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fd : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable fe : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable ff : Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z -> Z.
Variable getbit : Z -> Z -> Z.

Definition step_gen (z x:Z) (n:nat) k : (Z * Z * Z * Z * Z * Z)
  := match k with  (a,b,c,d,e,f) =>
      let r := getbit (Z.of_nat n) z in
      (fa r a b c d e f x,
        fb r a b c d e f x,
        fc r a b c d e f x,
        fd r a b c d e f x,
        fe r a b c d e f x,
        ff r a b c d e f x)
      end.

End ScalarRec.