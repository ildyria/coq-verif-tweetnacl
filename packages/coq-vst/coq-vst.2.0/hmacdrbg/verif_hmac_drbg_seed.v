Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.floyd.sublist.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_pure_lemmas.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import VST.floyd.library.

Require Import hmacdrbg.verif_hmac_drbg_seed_common.

Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque initial_key. Opaque initial_value.
Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque list_repeat. 

Lemma body_hmac_drbg_seed_256: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed hmac_drbg_seed_inst256_spec.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [HDlen1 [HDlen2 [HData RES]]]. destruct handle_ss as [handle ss]. simpl in RES.
  
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite ptrofs_add_repr_0_r.
  freeze [0;2;3;4;5;6] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, Vint (Int.repr 1), info).

  Intros v. rename H into Hv.
  freeze [0] FR1.
  forward. thaw FR1.
  forward_if (
     PROP (v=0)
   LOCAL (temp _ret (Vint (Int.repr v)); temp _t'2 (Vint (Int.repr v));
   temp _ctx (Vptr b i); temp _md_info info; temp _len (Vint (Int.repr len));
   temp _custom data; gvar sha._K256 kv)
   SEP ( (EX p : val, !!malloc_compatible (sizeof (Tstruct _hmac_ctx_st noattr)) p &&
          memory_block Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (info,(M2,p)) (Vptr b i));
         FRZL FR0)).
  { destruct Hv; try omega. rewrite if_false; trivial. clear H. subst v.
    forward. Exists (Int.repr (-20864)).
    rewrite Int.eq_true.
    entailer!. thaw FR0. cancel.
    unfold_data_at 2%nat. thaw FIELDS. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite ptrofs_add_repr_0_r; trivial. }
  { subst v. clear Hv. simpl. forward. entailer!. }
  Intros. subst v. clear Hv. Intros p. rename H into MCp. simpl in MCp.

  (*Alloction / md_setup succeeded. Now get md_size*)
  deadvars!.
  forward_call tt.

  (*call mbedtls_md_hmac_starts( &ctx->md_ctx, ctx->V, md_size )*)
  thaw FR0. subst.
  assert (ZL_VV: Zlength initial_key =32) by reflexivity.
  thaw FIELDS.
  freeze [4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;2;5;6;7;9] FR2.
  replace_SEP 1 (UNDER_SPEC.EMPTY p).
  { entailer!. 
    eapply derives_trans. 2: apply UNDER_SPEC.mkEmpty.
    rewrite data_at__memory_block. simpl. entailer!. 
  }
  forward_call (Vptr b i, ((info,(M2,p)):mdstate), 32, initial_key, kv, b, Ptrofs.add i (Ptrofs.repr 12)).
  { simpl. cancel. }
  { split; trivial. red. simpl. rewrite int_max_signed_eq.
    split. trivial. split. omega. rewrite two_power_pos_equiv.
    replace (2^64) with 18446744073709551616. omega. reflexivity.
    apply isbyteZ_initialKey.
  }
  Intros. clear H.

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4] FR3.
  forward_call (Tsh, Vptr b (Ptrofs.add i (Ptrofs.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives.
     - apply data_at_memory_block.
     - cancel. }

  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at Tsh t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
    entailer!. rewrite field_at_data_at.
    simpl. rewrite field_compatible_field_address by auto with field_compatible. simpl.
    rewrite ptrofs_add_repr_0_r.
    cancel.
  }
  thaw FIELDS1. forward.
  freeze [0;4;5;6;7] FIELDS2.
  freeze [0;1;2;3;4;5;6;7;8;9] ALLSEP.

  forward_if
  (PROP ( )
   LOCAL (temp _md_size (Vint (Int.repr 32)); temp _ctx (Vptr b i); temp _md_info info;
   temp _len (Vint (Int.repr (Zlength Data))); temp _custom data; gvar sha._K256 kv;
   temp _t'4 (Vint (Int.repr 32)))
   SEP (FRZL ALLSEP)).
  { elim H; trivial. }
  { clear H.
    forward_if.
    + elim H; trivial. 
    + clear H. forward. forward. entailer!.  }
  forward. 
  deadvars!. (*drop_LOCAL 7%nat.  _t'4 *)

  (*NEXT INSTRUCTION:  ctx->entropy_len = entropy_len * 3 / 2*)
  thaw ALLSEP. thaw FIELDS2. forward.

  assert (FOURTYEIGHT: Int.unsigned (Int.mul (Int.repr 32) (Int.repr 3)) / 2 = 48).
  { rewrite mul_repr. simpl.
    rewrite Int.unsigned_repr. reflexivity. rewrite int_max_unsigned_eq; omega. }
  set (myABS := HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000) in *.
  assert (myST: exists ST:hmac256drbgstate, ST =
    ((info, (M2, p)), (map Vint (list_repeat 32 Int.one), (Vint (Int.repr rc),
        (Vint (Int.repr 48), (Val.of_bool pr_flag, Vint (Int.repr 10000))))))). eexists; reflexivity.
  destruct myST as [ST HST].

  freeze [0;1;2;3;4] FR_CTX.
  freeze [3;4;6;7;8] KVStreamInfoDataFreeBlk.

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;2;3] INI.
  specialize (Forall_list_repeat isbyteZ 32 1); intros IB1.
  replace_SEP 0 (
         data_at Tsh t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { entailer!. thaw INI. clear - FC_V IB1. (*KVStreamInfoDataFreeBlk.*) thaw FR_CTX.
    apply andp_right. apply prop_right. repeat split; trivial. apply IB1. split; omega.
    unfold_data_at 2%nat. 
    cancel. unfold md_full; simpl.
    rewrite field_at_data_at; simpl.
    unfold field_address. rewrite if_true; simpl; trivial.
    cancel.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [3;7] OLD_MD.
  forward_call (Data, data, Zlength Data, Vptr b i, ST, myABS, kv, Info, s).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { subst myABS; simpl. rewrite <- initialize.max_unsigned_modulus in *; rewrite hmac_pure_lemmas.ptrofs_max_unsigned_eq.
    split. omega. (* rewrite int_max_unsigned_eq; omega.*)
    split. reflexivity.
    split. reflexivity.
    split. omega.
    split. (*change Int.modulus with 4294967296.*) omega.
    split. (* change Int.modulus with 4294967296.*)
       unfold contents_with_add. if_tac. omega. rewrite Zlength_nil; omega.
    split. apply IB1. split; omega.
    assumption.
  }

  Intros v.
  assert (ZLc': Zlength (contents_with_add data (Zlength Data) Data) = 0 \/
                 Zlength (contents_with_add data (Zlength Data) Data) = Zlength Data).
         { unfold contents_with_add. if_tac. right; trivial. left; trivial. }
  forward.
  deadvars!. 
  forward_if (
   PROP ( v = nullval)
   LOCAL (temp _ret v; temp _t'7 v;
   temp _entropy_len (Vint (Int.repr 32)); temp _ctx (Vptr b i);
   gvar sha._K256 kv)
   SEP (reseedPOST v Data data (Zlength Data) s
          myABS (Vptr b i) Info kv ST; FRZL OLD_MD)).
  { rename H into Hv. forward. simpl. Exists v.
    apply andp_right. apply prop_right; split; trivial.
    unfold reseedPOST.

    remember ((zlt 256 (Zlength Data) || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data)) %bool) as d.
    unfold myABS in Heqd; simpl in Heqd.
    destruct (zlt 256 (Zlength Data)); simpl in Heqd.
    + omega.
    + destruct (zlt 384 (48 + Zlength Data)); simpl in Heqd; try omega.
      subst d.
      unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl. Intros.
      rename H into RV.
      remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
      rewrite (ReseedRes _ _ _ RV). cancel.
      unfold return_value_relate_result in RV.
      assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { apply Zgt_is_gt_bool_f. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; trivial. omega. }
      unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer.
      destruct MRS.
      - exfalso. inv RV. simpl in Hv. discriminate.
      - simpl. Intros. Exists p. thaw OLD_MD. cancel.
        subst myABS. rewrite <- instantiate256_reseed in HeqMRS; trivial.
        rewrite RES in HeqMRS. inv HeqMRS. 
  }
  { rename H into Hv. forward. entailer!. 
    apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv; subst v. trivial.
  }
  deadvars!. Intros. subst v. unfold reseedPOST. 

  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros.

  assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { destruct ZLc' as [HH | HH]; rewrite HH. reflexivity.
        apply Zgt_is_gt_bool_f. omega. }
  subst myABS.
  rewrite <- instantiate256_reseed, RES; trivial. clear - RES HST ZLc'256F.
  destruct handle as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds.
  simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl.
  unfold_data_at 1%nat. 
  freeze [0;1;2;4;5;6;7;8;9;10;11;12;13] ALLSEP.
  forward. forward.
 
  Exists Int.zero. simpl.
  apply andp_right. apply prop_right; split; trivial. 
  Exists p. 
  thaw ALLSEP. thaw OLD_MD. rewrite <- instantiate256_reseed, RES; trivial. simpl. 
  cancel; entailer!.
  unfold_data_at 1%nat. cancel.
  apply hmac_interp_empty.
Time Qed. (*Coq8.6: 32secs*)
