Require Import Tweetnacl.Libs.Export.

Definition Zgetbit (i:Z) (l: Z) := Z.land (Z.shiftr l i) 1.