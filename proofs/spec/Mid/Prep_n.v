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

(* Eval compute in (ZofList 8 [Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;
Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;
Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;
Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;127]). *)
(* Eval compute in Z.ones 255.
(* 57896044618658097711785492504343953926634992332820282019728792003956564819967 *) *)
(* Eval compute in (ZofList 8 [248;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;
Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;
Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;
Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;Z.ones 8;127]). *)
(* 57896044618658097711785492504343953926634992332820282019728792003956564819960 *)

(* Eval compute in Z.land (Z.ones 255) (-8). *)
(* Definition Zclamp' (n : Z) : Z :=
  (Z.lor (Z.land n 57896044618658097711785492504343953926634992332820282019728792003956564819960) (Z.shiftl 64 (31 * 8))).
*)
Definition Zclamp (n : Z) : Z :=
  (Z.lor (Z.land n (Z.land (Z.ones 255) (-8))) (Z.shiftl 64 (31 * 8))).

(*
Lemma Zclamp_eq : forall n,
  Zclamp' n = Zclamp n.
Proof. done. Qed.
*)
Lemma Zclamp_min n : 0 <= Zclamp n.
Proof.
rewrite /Zclamp.
apply Z.lor_nonneg; split => //.
apply Z.land_nonneg ; right => //.
Qed.

Lemma Zclamp_max n : Zclamp n < 2^255.
Proof.
rewrite /Zclamp.
apply Z_lor_bound => //.
have ->: Z.land n 57896044618658097711785492504343953926634992332820282019728792003956564819960 = Z.land (Z.land n 57896044618658097711785492504343953926634992332820282019728792003956564819960) (Z.ones 255).
rewrite -Z.land_assoc => //=.
rewrite Z.land_ones => //.
apply Z_mod_lt => //.
Qed.

Close Scope Z.