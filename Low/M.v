Require Import Tweetnacl.Libs.Export.
Require Export Tweetnacl.Low.M_low_level_compute.
Require Export Tweetnacl.Low.Inner_M1.
Require Export Tweetnacl.Low.Outer_M1.
Require Export Tweetnacl.Mid.M_low_level.
Require Export Tweetnacl.Mid.M.
Require Export Tweetnacl.Mid.ScalarMult.
Require Export Tweetnacl.Low.Car25519.
Require Export Tweetnacl.Mid.Car25519.


Definition M (a b o : list Z) : list Z := (car25519 (car25519 (M3_fix (Z.of_nat 16%nat)
                  (M2_fix (Z.of_nat 15%nat)
                    (M1_fix a b)
                  )
                  o))).