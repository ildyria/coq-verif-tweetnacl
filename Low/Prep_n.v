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

Definition clamp (n : list Z) : list Z :=
  upd_nth 0 (upd_nth 31 n (Z.lor (Z.land (nth 31 n 0) 127) 64)) (Z.land (nth 0 n 0) 248).

Lemma clamp_bound : forall l,
    Forall (fun x => 0 <= x < Z.pow 2 8) l ->
    Forall (fun x => 0 <= x < Z.pow 2 8) (clamp l).
Proof.
move=> l HForall.
unfold clamp.
assert(HForall_inf_supp: Forall (λ x : ℤ, 0 ≤ x) l /\ Forall (λ x : ℤ, x < 2 ^ 8) l)
  by (split ; eapply Forall_impl ; eauto; intros ; simpl in H ; omega).
destruct HForall_inf_supp as [HForall_inf HForall_sup].
apply upd_nth_Forall.
apply upd_nth_Forall.
assumption.
rewrite Z.lor_land_distr_l ; simpl.
split.
apply Z.land_nonneg ; right ; omega.
change 127 with (Z.ones 7).
orewrite Z.land_ones.
assert(Z.lor (nth 31 l 0) 64 `mod` 2 ^ 7 < 2 ^ 7) by (apply Z_mod_lt; reflexivity).
assert(2 ^ 7 < 2 ^ 8) by reflexivity.
omega.
split.
apply Z.land_nonneg.
omega.
apply Z.log2_lt_cancel .
eapply Z.le_lt_trans.
apply Z.log2_land.
apply Forall_nth_d.
omega.
assumption.
omega.
apply Z.min_lt_iff.
right.
reflexivity.
Qed.

Lemma clamp_length : forall l, 
  (length l = 32)%nat -> (length (clamp l) = 32)%nat.
Proof. move => l Hl ; rewrite /clamp ?upd_nth_length ; omega. Qed.

Lemma clamp_Zlength : forall l, 
  Zlength l = 32 -> Zlength (clamp l) = 32.
Proof. convert_length_to_Zlength clamp_length. Qed.

Close Scope Z.