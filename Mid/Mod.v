From Tweetnacl Require Import Libs.Export.

Definition modP x := Z.modulo x (Z.pow 2 255 - 19).
