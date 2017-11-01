Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
Local Open Scope Z.

(* upd_Znth 0
                 (upd_Znth 31 (map (fun x : ℤ => Vint (Int.repr x)) (firstn 31 contents_n) ++ [Vundef])
                    (Vint
                       (Int.zero_ext 8
                          (Int.or (Int.and (Int.repr (Znth 31 contents_n 0)) (Int.repr 127)) (Int.repr 64)))))
                 (Vint
                    (cast_int_int I8 Unsigned
                       (Int.and (Int.repr (Znth 0 (firstn 31 contents_n) 0)) (Int.repr 248))))
 *)
(*
z = n
z[31]=(n[31]&127)|64;
z[0]&=248;
*)

Definition clamp (n : list Z) : list Z :=
  upd_nth 0 (upd_nth 31 n (Z.lor (Z.land (nth 31 n 0) 127) 64)) (Z.land (nth 0 n 0) 248).

Close Scope Z.