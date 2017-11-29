Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Libs.HeadTailRec.
Section ScalarRec.

Variable fa : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fb : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fc : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fd : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable fe : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable ff : Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Definition step_gen (z x:list Z) (n:nat) k : (list Z * list Z * list Z * list Z * list Z * list Z)
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