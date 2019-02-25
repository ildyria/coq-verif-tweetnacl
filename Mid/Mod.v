From Tweetnacl Require Import Libs.Export.
Require Import ssreflect.

Local Open Scope Z.
Definition modP x := Z.modulo x (Z.pow 2 255 - 19).
