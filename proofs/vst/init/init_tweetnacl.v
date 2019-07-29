Set Warnings "-notation-overridden,-parsing".
From VST Require Export floyd.proofauto. (* Import the Verifiable C system *)
From Tweetnacl_verif Require Export tweetnaclVerifiableC.
From Tweetnacl.Low Require Import Constant.

(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* Save current normalize *)
Ltac normalize_VST :=  try match goal with |- context[subst] =>  autorewrite with subst typeclass_instances end;
 try match goal with |- context[ret_assert] =>  autorewrite with ret_assert typeclass_instances end;
 match goal with
 | |- semax _ _ _ _ =>
  floyd.seplog_tactics.normalize;
  repeat
  (first [ simpl_tc_expr
         | simple apply semax_extract_PROP; fancy_intros true
         | move_from_SEP
         ]; cbv beta; msl.log_normalize.normalize)
  | |- _  =>
    floyd.seplog_tactics.normalize
  end.

(* idtac the current one: hope for speed. *)
Ltac normalize ::= idtac.
(* This is way way too agressive. *)
(* Ltac safe_subst_any ::= idtac. *)


Notation tlg := (Tlong Signed {| attr_volatile := false; attr_alignas := Some 3%N |}).
Notation uch32 := (tarray tuchar 32).
Notation lg16 := (tarray tlg 16).
Notation mVI64 l := (map Vlong (map Int64.repr l)).
Notation mVI l := (map Vint (map Int.repr l)).
Notation "S [{ A }] <<( T )-- B" := (data_at S T B A) (A at level 50, left associativity, at level 50).
Notation gf1 := Low.C_1.
Notation gf0 := Low.C_0.
Notation gf0_31 :=
  (0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 0 ::
  0 :: 0 :: 0 :: 0 :: 0 :: 0 :: nil).

Definition nm_overlap_array_sep_2 sho sha (o' a':list val) (o a:val) (k:Z) :=
  if (Z.eqb k 0) then
     !!(o'=a' /\ o = a) && (sho [{o}] <<(lg16)-- o')
  else ((sho [{o}] <<(lg16)-- o') * (sha [{a}] <<(lg16)-- a')):mpred.

Definition nm_overlap_array_sep_2' sho sha (o' a':list val) (o a:val) (k:Z) : mpred :=
  if (Z.eqb k 0) then (sho [{o}] <<(lg16)-- o')
  else ((sho [{o}] <<(lg16)-- o') * (sha [{a}] <<(lg16)-- a')):mpred.

Definition nm_overlap_array_sep_3 sho sha shb (o':list val) (a' b':list Z) o a b k: mpred :=
  if (Z.eqb k 0)
  then (!!(o'= mVI64 a' /\ o = a) && (sho [{o}] <<(lg16)-- o')) * (shb [{b}] <<(lg16)-- mVI64 b')
  else if (Z.eqb k 1)
  then (!!(o'= mVI64 b' /\ o = b) && (sho [{o}] <<(lg16)-- o')) * (sha [{a}] <<(lg16)-- mVI64 a')
  else if (Z.eqb k 2)
  then (!!(a'=b' /\ a = b) && (sho [{o}] <<(lg16)-- o')) * (sha [{a}] <<(lg16)-- mVI64 a')
  else if (Z.eqb k 3)
  then (!!(a'=b'  /\ o' = mVI64 a' /\ a = b /\ o = a ) && (sho [{o}] <<(lg16)-- o'))
  else (sho [{o}] <<(lg16)-- o') * (sha [{a}] <<(lg16)-- mVI64 a') * (shb [{b}] <<(lg16)-- mVI64 b').

Definition nm_overlap_array_sep_3' sho sha shb (o' a' b':list val) o a b k: mpred :=
  if (Z.eqb k 0)
  then ((sho [{o}] <<(lg16)-- o')) * (shb [{b}] <<(lg16)-- b')
  else if (Z.eqb k 1)
  then ((sho [{o}] <<(lg16)-- o')) * (sha [{a}] <<(lg16)-- a')
  else if (Z.eqb k 2)
  then ((sho [{o}] <<(lg16)-- o')) * (sha [{a}] <<(lg16)-- a')
  else if (Z.eqb k 3)
  then (sho [{o}] <<(lg16)-- o')
  else (sho [{o}] <<(lg16)-- o') * (sha [{a}] <<(lg16)-- a') * (shb [{b}] <<(lg16)-- b').

Ltac unfold_nm_overlap_array_sep :=
  unfold nm_overlap_array_sep_2; unfold nm_overlap_array_sep_2';
  unfold nm_overlap_array_sep_3; unfold nm_overlap_array_sep_3';
  repeat match goal with 
  | [ H : (_ =? _ ) = true |- _ ] => rewrite H
  | [ H : (_ =? _ ) = false |- _ ] => rewrite H
end.

Ltac prep_forward :=
  repeat match goal with
    | [ H : ?i = ?i |- _ ] => clear H
   end.

Ltac freeze_local L :=
  deadvars!;
  match goal with
    [ |- semax _ (PROPx _ (LOCALx ?l _)) _ _ ] => remember l as L
  end.

Ltac data_atify := repeat match goal with
  | |- context[field_at ?A ?B _ ?D ?E] => change (field_at A B [] D E) with (data_at A B D E)
end.

Ltac thaw_local := auto 50 with closed.

Ltac replace_cancel :=
  unfold data_at ;
  match goal with
  | [ |- _ (_ _ _ _ ?a _) (_ _ _ _ ?b _)] => replace a with b
  end; try cancel.

Ltac clean_context_from_VST :=
  repeat match goal with
    | [H : context[writable_share] |- _ ]     => clear H
    | [H : context[readable_share] |- _ ]     => clear H
    | [H : context[isptr] |- _ ]              => clear H
    | [H : context[headptr] |- _ ]            => clear H
    | [H : context[is_pointer_or_null] |- _ ] => clear H
    | [H : context[is_long] |- _ ]            => clear H
    | [H : context[is_int] |- _ ]             => clear H
    | [H : context[field_compatible] |- _ ]   => clear H
    | [H : context[value_fits] |- _ ]         => clear H
    | [H : context[ret_assert]  |- _ ]        => clear H
    | [H : context[tycontext]  |- _ ]         => clear H
    | [H : context[statement]  |- _ ]         => clear H
    | [H : context[PTree.t funspec]  |- _ ]   => clear H
    | [H : context[OracleKind]  |- _ ]        => clear H
    | [H : context[list mpred]  |- _ ]        => clear H
    | _ => idtac
  end.

From Tweetnacl_verif Require Export missing_lemmae.
From Tweetnacl Require Export Libs.Export.

Ltac unfolds_set_sep := unfold nm_overlap_array_sep_3, nm_overlap_array_sep_3'.
Ltac unfold_entail := unfolds_set_sep; flatten; entailer!.


Definition set_undef_array_sep sh cst i (o':list val) (o:val) : mpred :=
  if Z.eqb cst i then
     sh [{o}] <<(lg16)-- undef16
  else sh [{o}] <<(lg16)-- o'.

Open Scope Z.

Lemma Znth_g0 : forall i,
  0 <= i < 16 ->
  Vlong (Int64.repr 0) = Znth i (mVI64 gf0) Vundef.
Proof.
intros.
gen_i Hi i;  reflexivity. (* sometimes it is faster to bruteforce ... *)
Qed.

Lemma Znth_nil16 : forall i,
  0 <= i < 16 ->
  Vlong (Int64.repr 0) = Znth i (mVI64 nil16) Vundef.
Proof.
intros;
rewrite (Znth_map Int64.zero) ; f_equal;
rewrite ?(Znth_map 0); f_equal;
rewrite ?Znth_list_repeat_inrange ?Zlength_map ?nil16_Zlength ; try omega.
Qed.

Require Export ssreflect.
