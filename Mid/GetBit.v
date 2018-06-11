Require Import Tweetnacl.Libs.Export.

Definition Zgetbit (i:Z) (l: Z) := if (Z.ltb i 0) then
  Z.land l 1
  else
  Z.land (Z.shiftr l i) 1.