Require Import stdpp.list.
Require Import ssreflect.
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

(* Eval compute in Z.ones 255. *)
(* 57896044618658097711785492504343953926634992332820282019728792003956564819967 *)

Definition ZUnpack25519 (n : Z) : Z := Z.land n (Z.ones 255).

Lemma Zunpack_bounded: forall x, 0 <= x < 2^255 - 19 -> 0 <= ZUnpack25519 x < 2 ^ 255 - 19.
Proof.
move => x Hx.
rewrite /ZUnpack25519.
rewrite Z.land_ones //=.
rewrite Zmod_small //=.
split ; omega.
Qed.
