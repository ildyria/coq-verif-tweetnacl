Require Import Tweetnacl.Libs.Export.
Require Export Tweetnacl.Low.M.

Definition S (a o : list Z) : list Z := M a a o.