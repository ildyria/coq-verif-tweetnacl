Require Import Tweetnacl.Libs.Export.

Open Scope Z.

Module Mid.
Definition getbit (i:Z) (l: Z) := 
  if (Z.ltb l 0) then
    0
  else
  if (Z.ltb i 0) then
  Z.land l 1
  else
  Z.land (Z.shiftr l i) 1.

End Mid.
Close Scope Z.