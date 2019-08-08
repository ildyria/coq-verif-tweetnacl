Require Import Tweetnacl.Libs.Export.

Open Scope Z.

Module Mid.
Definition getbit (i:Z) (a: Z) := 
  if (Z.ltb a 0) then
    0
  else
  if (Z.ltb i 0) then
  Z.land a 1
  else
  Z.land (Z.shiftr a i) 1.

End Mid.
Close Scope Z.