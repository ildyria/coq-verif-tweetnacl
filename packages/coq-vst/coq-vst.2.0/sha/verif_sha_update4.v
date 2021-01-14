Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.verif_sha_update3.
Local Open Scope Z.
Local Open Scope logic.

Lemma Hblocks_lem:
 forall {blocks: list int} {frag: list Z} {data},
 intlist_to_Zlist blocks = frag ++ sublist 0 (Zlength blocks * 4 - Zlength frag) data ->
 Zlength frag <= Zlength blocks * 4.
Proof.
intros.
assert (Zlength (intlist_to_Zlist blocks) =
               Zlength ( frag ++
     sublist 0 (Zlength blocks * 4 - Zlength frag) data)) by congruence.
 autorewrite with sublist in H0.
 pose proof (Zlength_nonneg (sublist 0 (Zlength blocks * 4 - Zlength frag) data)).
 omega.
Qed.

Definition sha_update_loop_body :=
  (Ssequence
     (Scall None
        (Evar _sha256_block_data_order
           (Tfunction
              (Tcons (tptr t_struct_SHA256state_st) (Tcons (tptr tvoid) Tnil))
              tvoid cc_default))
        [Etempvar _c (tptr t_struct_SHA256state_st);
        Etempvar _data (tptr tuchar)])
     (Ssequence
        (Sset _data
           (Ebinop Oadd (Etempvar _data (tptr tuchar))
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) (tptr tuchar)))
        (Sset _len
           (Ebinop Osub (Etempvar _len tuint)
              (Ebinop Omul (Econst_int (Int.repr 16) tint)
                 (Econst_int (Int.repr 4) tint) tint) tuint)))).

Definition update_outer_if :=
     Sifthenelse
        (Ebinop Cop.One (Etempvar _n tuint) (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
           (Sset _fragment
              (Ebinop Osub
                 (Ebinop Omul (Econst_int (Int.repr 16) tint)
                    (Econst_int (Int.repr 4) tint) tint) (Etempvar _n tuint)
                 tuint)) update_inner_if)
        Sskip.

Lemma update_outer_if_proof:
 forall  (Espec : OracleKind) (hashed : list int)
           (dd data : list Z) (c d : val) (sh : share) (len : Z) kv
   (H : 0 <= len <= Zlength data)
   (Hsh: readable_share sh)
   (HBOUND : bitlength hashed dd + len * 8 < two_p 64)
   (H3 : Zlength dd < CBLOCKz)
   (H3' : Forall isbyteZ dd)
   (H4 : (LBLOCKz | Zlength hashed))
   (Hlen : len <= Int.max_unsigned),
semax
  (initialized_list [_data; _p; _n]
     (func_tycontext f_SHA256_Update Vprog Gtot))
  (PROP  ()
   LOCAL
   (temp _p (field_address t_struct_SHA256state_st [StructField _data] c);
    temp _n (Vint (Int.repr (Zlength dd)));
    temp _data d; temp _c c;temp _data_ d;
    temp _len (Vint (Int.repr len));
    gvar _K256 kv)
   SEP  (data_at Tsh t_struct_SHA256state_st
                 (map Vint (hash_blocks init_registers hashed),
                  (Vint (lo_part (bitlength hashed dd + len*8)),
                   (Vint (hi_part (bitlength hashed dd + len*8)),
                    (map Vint (map Int.repr dd) ++ list_repeat (Z.to_nat (CBLOCKz-Zlength dd)) Vundef,
                     Vint (Int.repr (Zlength dd))))))
               c;
     K_vector kv;
     data_block sh data d))
  update_outer_if
  (overridePost (sha_update_inv sh hashed len c d dd data kv false)
    (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX  a' : s256abs,
         PROP  (update_abs (sublist 0 len data) (S256abs hashed dd) a')
         LOCAL ()
         SEP  (K_vector kv;
                 sha256state_ a' c; data_block sh data d)))
    emp)).
Proof.
intros.
unfold update_outer_if.
forward_if (sha_update_inv sh hashed len c d dd data kv false).
* (* then clause *)

Time forward.  (* fragment = SHA_CBLOCK-n; *) (*2.2*)
  pose proof CBLOCKz_eq. pose proof (Zlength_nonneg dd). 
  entailer!.
drop_LOCAL 5%nat.
rewrite semax_seq_skip.
fold (inv_at_inner_if sh hashed len c d dd data kv).
apply semax_seq with (sha_update_inv sh hashed len c d dd data kv false).
change Delta with Delta_update_inner_if.
weak_normalize_postcondition.
normalize. change (16*4)%Z with 64.
simple apply (update_inner_if_proof Espec hashed dd data c d sh len kv);
  try assumption.
forward.
apply andp_left2; auto.
* (* else clause *)
forward.  (* skip; *)
Exists (@nil int). rewrite <- app_nil_end.
apply repr_inj_unsigned in H0; try Omega1. rename H0 into H1.
rewrite H1 in *.
rewrite Zlength_correct in H1;  destruct dd; inv H1.
autorewrite with sublist.
simpl intlist_to_Zlist.
Time entailer!.  (* 4.6; was: 139 sec -> 3.27 sec *)
split.
apply Z.divide_0_r.
rewrite field_address0_offset by auto with field_compatible.
simpl. normalize.

(* TODO:  see if a "stronger" proof system could work here
  rewrite data_at_field_at.
   apply field_at_stronger.
  ...
  with automatic cancel...
*)
 Time unfold_data_at 1%nat. (*0.7*)
 Time unfold_data_at 1%nat. (*0.8*)
 Time cancel. (*0.4*)
Time Qed. (*5.4*)

Lemma update_while_proof:
 forall (Espec : OracleKind) (hashed : list int) (dd data: list Z) kv
    (c d : val) (sh : share) (len : Z)
  (H : 0 <= len <= Zlength data)
   (Hsh: readable_share sh)
  (HBOUND : bitlength hashed dd + len * 8 < two_p 64)
  (H3 : Zlength dd < CBLOCKz)
  (H3' : Forall isbyteZ dd)
  (H4 : (LBLOCKz | Zlength hashed))
  (Hlen : len <= Int.max_unsigned),
 semax
     (initialized_list [_p; _n; _data]
       (func_tycontext f_SHA256_Update Vprog Gtot))
  (sha_update_inv sh hashed len c d dd data kv false)
  (Swhile
     (Ebinop Oge (Etempvar _len tuint)
        (Ebinop Omul (Econst_int (Int.repr 16) tint)
           (Econst_int (Int.repr 4) tint) tint) tint) sha_update_loop_body)
  (normal_ret_assert (sha_update_inv sh hashed len c d dd data kv true)).
Proof.
intros.
abbreviate_semax.
unfold sha_update_inv.
Intros blocks.
rewrite semax_seq_skip. (* should be part of forward_while *)
forward_while
    (sha_update_inv sh hashed len c d dd data kv false);
  try rename blocks0 into blocks'.
*
 Exists blocks. entailer!.
*
  entailer!.
*
 clear H8.
 normalize_postcondition.
 clear dependent blocks.
 rename blocks' into blocks.
 pose proof (Hblocks_lem H7).
 assert (H0': (Zlength dd <= Zlength blocks * 4)%Z) by Omega1.
 clear H0; rename H0' into H0.
 rewrite Int.unsigned_repr in HRE by omega.
 assert_PROP (Forall isbyteZ data) as BYTESdata
  by (rewrite (data_block_isbyteZ sh data d); entailer!).
 pose (bl := Zlist_to_intlist (sublist (Zlength blocks * 4 - Zlength dd)
                                                   (Zlength blocks * 4 - Zlength dd + CBLOCKz) data)).
assert (Zlength bl = LBLOCKz). {
 apply Zlength_Zlist_to_intlist.
 pose proof CBLOCKz_eq; pose proof LBLOCKz_eq;
  autorewrite with sublist. reflexivity.
}
 {
  rename H6 into Hdiv. rename H7 into Hblocks. rename H0 into H7.
  rename HRE into Hlen_ge.  clear H5.
  assert (H6: sublist (Zlength blocks * 4 - Zlength dd)
                    (Zlength blocks * 4 - Zlength dd + CBLOCKz) data =
        intlist_to_Zlist bl).
  unfold bl; rewrite Zlist_to_intlist_to_Zlist; auto.
  pose proof CBLOCKz_eq;  autorewrite with sublist.
  exists LBLOCKz; reflexivity.
  rename dd into frag.
  clear H7; rename H1 into H7.
  rename HBOUND into LEN64.
  clear - Hsh H Hdiv H4 Hblocks H3 Hlen Hlen_ge H6 H7 LEN64.
  unfold sha_update_loop_body.
  assert (Hblocks' := Hblocks_lem Hblocks).
  Time assert_PROP (field_compatible (tarray tuchar (Zlength data)) [] d) as FC by entailer!. (*1.8*)
  assert (DM: Zlength data < Ptrofs.modulus).
  { (* TODO: simplify this proof. *)
    clear - FC. red in FC. simpl in FC. destruct d; try tauto.
    simpl in FC.
    rewrite Z.max_r in FC by (specialize (Zlength_nonneg data); intros; omega).
    inv_int i.
    rewrite Z.mul_1_l in FC.
    omega.
  }
  set (lo := Zlength blocks * 4 - Zlength frag) in *.
  replace_SEP 2
    (data_block sh (sublist 0 lo data) d *
       data_block sh (sublist lo (lo+CBLOCKz) data)
         (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc lo] d) *
       data_block sh (sublist (lo+CBLOCKz) (Zlength data) data)
         (field_address0 (tarray tuchar (Zlength data)) [ArraySubsc (lo+CBLOCKz)] d)).
  { Time entailer!. (*2.5*)
   rewrite (split3_data_block lo (lo+CBLOCKz) sh data); auto;
     subst lo; Omega1.
  }
 rewrite H6.
 Time forward_call (* sha256_block_data_order (c,data); *)
   (hashed++ blocks,  bl, c,
    field_address0 (tarray tuchar (Zlength data))  [ArraySubsc lo] d,
    sh, kv). (*3.8*)
  { Time unfold_data_at 1%nat. (*0.8*)
    Time cancel. (*2.5*)
  }
 split3; auto. apply divide_length_app; auto.
 Time forward. (* data += SHA_CBLOCK; *) (*5*)
 simpl (temp _data _).
 Time forward. (* len  -= SHA_CBLOCK; *) (*6*)
 Exists (blocks++ bl).
 Time entailer!. (*17.4 SLOW*)
 subst lo. autorewrite with sublist.
 rewrite Z.mul_add_distr_r.
 {repeat split; auto.
  + Omega1.
  + rewrite H7; apply Z.divide_add_r; auto. apply Z.divide_refl.
  + rewrite intlist_to_Zlist_app.
      rewrite Hblocks; rewrite <- H6.
      rewrite app_ass.
      f_equal.
      rewrite <- sublist_split; try Omega1.
      f_equal. Omega1.
  + assert (0 <= Zlength blocks * 4 + Zlength bl * 4 - Zlength frag <= Zlength data)
         by Omega1.
      rewrite !field_address0_offset by auto with field_compatible.
      rewrite offset_offset_val.
      simpl. f_equal. Omega1.
  + f_equal. f_equal. Omega1.
 }
 Time unfold_data_at 1%nat. (*0.8*)
 rewrite (split3_data_block lo (lo+CBLOCKz) sh data d)
    by (auto; subst lo; try Omega1).
 rewrite app_ass.
 rewrite H6.
 Time cancel. (*1.2*)
 }
*
 assert  (Zlength blocks' * 4 >= Zlength dd).
   rewrite <- (Zlength_intlist_to_Zlist blocks').
   rewrite H7. autorewrite with sublist. Omega1.
 normalize in HRE.
 unfold sha_update_inv.
 clear dependent blocks.
 forward.
 Exists blocks'.
 Time entailer!. (*2.9*)
Time Qed. (*31.3 *)
