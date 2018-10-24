Require Import Tweetnacl.Libs.Export.

Open Scope Z.

Definition Zgetbit (i:Z) (l: Z) := 
  if (Z.ltb l 0) then
    0
  else
  if (Z.ltb i 0) then
  Z.land l 1
  else
  Z.land (Z.shiftr l i) 1.

Close Scope Z.