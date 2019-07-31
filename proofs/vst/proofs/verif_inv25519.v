Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_M.
Require Import Tweetnacl_verif.spec_S.
Require Import Tweetnacl_verif.spec_inv25519.
Require Import Tweetnacl_verif.spec_set25519.
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Inv25519.
Require Import Tweetnacl.Low.S.

Open Scope Z.
(*
sv inv25519(gf o,const gf i)
{
  gf c;
  int a;
  FOR(a,16) c[a]=i[a];
  for(a=253;a>=0;a--) {
    S(c,c);
    if(a!=2&&a!=4) M(c,c,i);
  }
  FOR(a,16) o[a]=c[a];
}
*)


(* Packaging the API spec all together. *)
Definition Gprog : funspecs :=
      ltac:(with_library prog [inv25519_spec; set25519_spec; M_spec; S_spec]).

Lemma body_sel25519: semax_body Vprog Gprog f_inv25519 inv25519_spec.
Proof.
start_function.
rewrite /data_at_ /field_at_ /default_val ; simpl.
unfold nm_overlap_array_sep_2.
flatten ; Intros.
subst o v_i.
1: forward_call (v_c,v_o,Tsh,sho,undef16,i).
2: forward_call (v_c,v_i,Tsh,shi,undef16,i).

1: forward_for 
(* Loop Invariant *)
(inv25519_Inv sho sho Tsh v_o v_o v_c (mVI64 i) i 0)
(* PreInc invariant *)
(inv25519_PreIncInv sho sho Tsh v_o v_o v_c (mVI64 i) i 0)
(* Loop postcondition *)
(inv25519_PostInv sho sho Tsh v_o v_o v_c (mVI64 i) i 0).
7: forward_for 
(* Loop Invariant *)
(inv25519_Inv sho shi Tsh v_o v_i v_c o i 1)
(* PreInc invariant *)
(inv25519_PreIncInv sho shi Tsh v_o v_i v_c o i 1)
(* Loop postcondition *)
(inv25519_PostInv sho shi Tsh v_o v_i v_c o i 1).
all: try rename a0 into a.

(* 6 goals generated *)
(* 1 *)
1,7: forward.
1,2: unfold inv25519_Inv.
1,2: Exists 253.
1,2: change (253 - 253) with 0.
1,2: rewrite pow_fn_rev_0.
1,2: entailer!.
1,2: unfold_nm_overlap_array_sep ; simpl.
1,2: entailer!.

(* 2 *)
1,6 : entailer!.

(* 3 *)
1,5: unfold_nm_overlap_array_sep.
1: change (0 =? 0) with true.
2: change (1 =? 0) with false.
1,2: flatten ; Intros.
1,2: assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) (pow_fn_rev (253 - a) 254 i i)) 
  by (apply pow_fn_rev_bound_Zlength ; assumption).
1,2: assert(Zlength (pow_fn_rev (253 - a) 254 i i) = 16) by (apply pow_fn_rev_Zlength ; assumption).
all: assert(HWTsh:= writable_share_top).
all: assert(HRTsh:= writable_readable_share HWTsh).
1,2: remember (pow_fn_rev (253 - a) 254 i i) as c0.
1,2: assert(Zlength (mVI64 c0) = 16) by (rewrite ?Zlength_map ; assumption).

1,2: forward_call (v_c, v_c, Tsh, Tsh, mVI64 c0, c0, 0).
1,4: unfold_nm_overlap_array_sep ; simpl ; entailer!.
1,3: repeat match goal with | [ |- _ /\ _ ] => split | _ => assumption end.
1,2: solve_bounds_by_values_Forall_impl.
1,2: unfold_nm_overlap_array_sep; simpl.

1,2: assert(Ha: a = 2 \/ a = 4 \/ (a <> 2 /\ a <> 4)) by omega.

(* case analysis *)
(* i = 2 *)
1,2: destruct Ha as [Ha|Ha] ; try subst a.
1: forward_if (PROP ( )
   LOCAL (temp _a (Vint (Int.repr 2)); temp _t'1 (Vint (Int.repr 0)); temp _o v_o; temp _i v_o; lvar _c (tarray tlg 16) v_c)
   SEP (Tsh [{v_c}]<<( lg16 )-- mVI64 (Low.S c0); sho [{v_o}]<<( lg16 )-- mVI64 i)).
5: forward_if (PROP ( )
   LOCAL (temp _a (Vint (Int.repr 2)); temp _t'1 (Vint (Int.repr 0)); temp _o v_o; temp _i v_i; lvar _c (tarray tlg 16) v_c)
   SEP (Tsh [{v_c}]<<( lg16 )-- mVI64 (Low.S c0); sho [{v_o}]<<( lg16 )-- o; shi [{v_i}]<<( lg16 )-- mVI64 i)).
1,5: exfalso; match goal with [ H : ?A <> ?A |- _ ] => by apply H end.
1,4: forward.
1,2: entailer!.
1,3: forward_if.
1,3: exfalso; match goal with [ H : ?A <> ?B |- _ ] => by apply H end.
1,2: forward.
1,2: rewrite /inv25519_PreIncInv.
1,2: unfold_nm_overlap_array_sep.
1: change (0 =? 0) with true.
2: change (1 =? 0) with false.
1,2: flatten.
1,2: Exists 2;
  orewrite pow_fn_rev_n;
  oreplace (253 - (2 - 1) - 1) (253 - 2);
  oreplace (254 - 1 - (253 - (2 - 1))) 1;
  subst c0;
  remember (pow_fn_rev (253 - 2) 254 a a) as c0;
  clear Heqc0;
  replace (step_pow 1 c0 a) with (Low.S c0); [entailer!|]; 
  rewrite /step_pow /Inv25519_gen.step_pow ;
  change (Zneq_bool 1 1 && Zneq_bool 1 3) with false ; flatten.
1,2: destruct Hi as [Hi|Hi] ; try subst i.
1: forward_if (PROP ( )
   LOCAL (temp _i (Vint (Int.repr 4)); temp _t'1 (Vint (Int.repr 0)); temp _o v_o; temp _a v_o; lvar _c (tarray tlg 16) v_c)
   SEP (data_at Tsh (tarray tlg 16) (mVI64 (Low.S c0)) v_c; data_at sho (tarray tlg 16) (mVI64 a) v_o)).
5: forward_if (PROP ( )
   LOCAL (temp _i (Vint (Int.repr 4)); temp _t'1 (Vint (Int.repr 0)); temp _o v_o; temp _a v_a; lvar _c (tarray tlg 16) v_c)
   SEP (Tsh [{v_c}]<<( lg16 )-- mVI64 (Low.S c0); sho [{v_o}]<<( lg16 )-- o; sha [{v_a}]<<( lg16 )-- mVI64 a)).
1,5: forward.
1,2: entailer!.
1,4: match goal with [ H : Int.one = Int.zero |- _ ] => inversion H end.
1,3: forward_if.
1,3: exfalso; match goal with [ H : ?A <> ?B |- _ ] => by apply H end.
1,2: forward.
1,2: rewrite /inv25519_PreIncInv.
1,2: unfold_nm_overlap_array_sep.
1: change (0 =? 0) with true.
2: change (1 =? 0) with false.
1,2: flatten.
1,2: Exists 4;
  orewrite pow_fn_rev_n;
  oreplace (253 - (4 - 1) - 1) (253 - 4);
  oreplace (254 - 1 - (253 - (4 - 1))) 3;
  subst c0;
  remember (pow_fn_rev (253 - 4) 254 a a) as c0;
  clear Heqc0;
  replace (step_pow 3 c0 a) with (Low.S c0); [entailer!|]; 
  rewrite /step_pow /Inv25519_gen.step_pow ;
  change (Zneq_bool 3 1 && Zneq_bool 3 3) with false ; flatten.
1,2: destruct Hi as [Hi2 Hi4].
1: forward_if (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i)); temp _t'1 (Vint (Int.repr 1)); temp _o v_o; temp _a v_o; lvar _c (tarray tlg 16) v_c)
   SEP (data_at Tsh (tarray tlg 16) (mVI64 (Low.S c0)) v_c; data_at sho (tarray tlg 16) (mVI64 a) v_o)).
4: forward_if (PROP ( )
   LOCAL (temp _i (Vint (Int.repr i)); temp _t'1 (Vint (Int.repr 1)); temp _o v_o; temp _a v_a; lvar _c (tarray tlg 16) v_c)
   SEP (Tsh [{v_c}]<<( lg16 )-- mVI64 (Low.S c0); sho [{v_o}]<<( lg16 )-- o; sha [{v_a}]<<( lg16 )-- mVI64 a)).
1,4: forward.
1,2: entailer!.
1,2: clean_context_from_VST ; simpl ;
replace (negb (Int.eq (Int.repr i) (Int.repr 4))) with true ; try reflexivity ;
replace (Int.eq (Int.repr i) (Int.repr 4)) with false ; try reflexivity ;
symmetry ; apply Int.eq_false;
intro Hifalse;
inversion Hifalse as [Hifalsee];
rewrite Int.Z_mod_modulus_eq in Hifalsee;
change (Int.modulus) with (4294967296) in Hifalsee;
rewrite Z.mod_small in Hifalsee ; omega.
1,3: exfalso ; omega.
1,2: forward_if.
2,4: exfalso; match goal with [ H : Int.repr 1 = Int.zero |- _ ] => inversion H end.
1: forward_call (v_c,v_c,v_o,Tsh,Tsh,sho,mVI64 (Low.S c0),Low.S c0,a, 0).
4: forward_call (v_c,v_c,v_a,Tsh,Tsh,sha,mVI64 (Low.S c0),Low.S c0,a, 0).
1,4: unfold_nm_overlap_array_sep ; simpl ; entailer!.
all: assert(HRsho:= writable_readable_share SH).
1,3: repeat match goal with | [ |- _ /\ _ ] => split | _ => assumption end.
1,2,4,5: solve_bounds_by_values_Forall_impl.
1,2: by rewrite ?Zlength_map.
1,2: rewrite /inv25519_PreIncInv.
1,2: unfold_nm_overlap_array_sep.
1,2: change (0 =? 0) with true.
1,2: change (1 =? 0) with false.
1,2: flatten.
1,2: Exists i.
1,2: entailer!.
1,2: replace ((Low.M (Low.S (pow_fn_rev (253 - i) 254 a a)) a)) with (pow_fn_rev (253 - (i - 1)) 254 a a).
1,3: cancel.
1,2: orewrite pow_fn_rev_n.
1,2: oreplace (253 - (i - 1) - 1) (253 - i).
1,2: oreplace (254 - 1 - (253 - (i - 1))) (i - 1).
1,2: rewrite /step_pow /Inv25519_gen.step_pow.
1,2: replace (Zneq_bool (i - 1) 1 && Zneq_bool (i - 1) 3) with true ; try reflexivity.
1,2: symmetry ; apply andb_true_iff.
1,2: split ; rewrite /Zneq_bool ; flatten ; apply Z.compare_eq_iff in Eq2; omega.

(* Goal 3 *)
1,4: forward.
1,2: Exists (i - 1).
1,2: entailer!.

(* Goal 4 *)
1,3: assert(i = -1) by omega.
1,2: subst i.
all: rewrite /inv25519_PostInv.
1,2: oreplace (253 - - 1) 254.
all: unfold_nm_overlap_array_sep.
all: change (0 =? 0) with true.
all: change (1 =? 0) with false.
all: flatten.
all: remember (pow_fn_rev 254 254 a a) as p. (* the expension is always anoying... *)
1,2: entailer!.

1,2: assert(Zlength (pow_fn_rev 254 254 a a) = 16) by (apply pow_fn_rev_Zlength ; assumption).

(* Goal 1 *)
1,2: freeze_local L.
(* rewrite {1}/Sfor. (* because forward_for_simple_bound does not work otherwise *) *)
1: forward_for_simple_bound 16 (copy_Inv L sho sha Tsh v_o v_o v_c (mVI64 a) a p 0) ; subst L.
1: thaw_local.
4: forward_for_simple_bound 16 (copy_Inv L sho sha Tsh v_o v_a v_c o a p 1) ; subst L.
4: thaw_local.
1,4: entailer!.
1,3: assert(Hd: exists d, Vlong d = Znth i (mVI64 p) Vundef) by
     (eexists ; rewrite map_map (Znth_map 0) ; subst p; try reflexivity ; omega).
1,2: destruct Hd as [d Hd].
1,2: subst p; remember (pow_fn_rev 254 254 a a) as p. (* the expension is always anoying... *)
all: unfold_nm_overlap_array_sep.
all: change (0 =? 0) with true.
all: change (1 =? 0) with false.
all: flatten ; Intros.
1,2: forward ; rewrite -Hd.
1,3: entailer!.
1,2: forward.
1,2: unfold_nm_overlap_array_sep.
1,2: change (0 =? 0) with true.
1,2: change (1 =? 0) with false.
1,2: flatten ; Intros.
1,2: entailer!.
1,2: unfold data_at ; replace_cancel.
1,2: repeat orewrite simple_S_i.
1,2: remember (pow_fn_rev 254 254 a a) as p.
1,2: rewrite (upd_Znth_app_step_Zlength i _ _ Vundef) ?Hd ; rewrite ?Zlength_map ; try omega ; reflexivity.
1: replace ((firstn (nat_of_Z 16) (mVI64 p) ++ skipn (nat_of_Z 16) (mVI64 a))) with (tkdp (Zlength (mVI64 p)) (mVI64 p) (mVI64 a)).
2: replace (Zlength (mVI64 p)) with 16 ; try reflexivity ; rewrite ?Zlength_map ; subst p ; omega.
2: replace ((firstn (nat_of_Z 16) (mVI64 p) ++ skipn (nat_of_Z 16) o)) with (tkdp (Zlength (mVI64 p)) (mVI64 p) o).
3: replace (Zlength (mVI64 p)) with 16 ; try reflexivity ; rewrite ?Zlength_map ; subst p ; omega.
1,2: rewrite tkdp_all.
2,4: rewrite ?Zlength_map ; subst p ; omega.
all: unfold_nm_overlap_array_sep.
all: unfold POSTCONDITION.
all: unfold abbreviate.
all: eapply (semax_return_None _ _ _ _ _ (stackframe_of f_inv25519) [Tsh [{v_c}]<<( lg16 )-- undef16]).
all: try reflexivity.
all: try apply return_outer_gen_refl.
all: try apply return_inner_gen_canon_nil.
all: try (eapply canonicalize_stackframe ; [ reflexivity| ]).
all: try (apply Forall2_cons; [apply fn_data_at_intro ; reflexivity |  apply Forall2_nil]).
all: match goal with | [ |- context[[?A] ++ [?B]] ] => change ([A] ++ [B]) with ([A ; B]) end.
all: unfold_nm_overlap_array_sep.
all: assert(Zlength (Inv25519 a) = 16) by (apply Inv25519_Zlength ; omega).
all: assert(Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) (Inv25519 a)) by (apply Inv25519_bound_Zlength ; assumption).
all: subst p ; replace (pow_fn_rev 254 254 a a) with (Inv25519 a) by reflexivity.
all: remember (Inv25519 a) as p.
all: rewrite Eq.
all: entailer!.
Qed.