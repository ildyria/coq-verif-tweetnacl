Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl_verif.init_tweetnacl.

Open Scope Z.

Import Low.

Definition M_spec :=
 DECLARE _M
  WITH v_o: val, v_a: val, v_b: val,
    sho : share, sha : share, shb : share,
    o : list val,
    a : list Z,
    b : list Z,
    k : Z
  PRE [ _o OF (tptr tlg), _a OF (tptr tlg), _b OF (tptr tlg) ]
        PROP  (writable_share sho; readable_share sha; readable_share shb;
                Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a;
                Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b;
                Zlength a = 16;
                Zlength b = 16;
                Zlength o = 16)
        LOCAL (temp _o v_o; temp _a v_a; temp _b v_b)
        SEP   (nm_overlap_array_sep_3 sho sha shb o a b v_o v_a v_b k)
  POST [ tvoid ]
        PROP (
          Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b))
        LOCAL()
        SEP ( nm_overlap_array_sep_3' sho sha shb (mVI64 (M a b)) (mVI64 a) (mVI64 b) v_o v_a v_b k).

Definition M_Tinit_Inv F L t := 
  EX i : Z,
   PROP  ()
   (LOCALx L
   SEP   (FRZL F ;
          Tsh [{ t }] <<(tarray tlg 31)-- (map Vlong (list_repeat (Z.to_nat i) Int64.zero) ++ list_repeat (Z.to_nat (31 - i)) Vundef))).

Definition M1_outer_Inv sho sha shb L v_o v_a v_b v_t o a b t k := 
  EX i : Z,
   PROP  (
(*           Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_a;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_b;
          Zlength contents_a = 16;
          Zlength contents_b = 16;
          Zlength contents_o = 16;
          Zlength contents_t = 31; *)
(*           i >= 0 *)
          )
   (LOCALx L
   SEP   (Tsh [{ v_t }] <<(tarray tlg 31)-- mVI64 (outer_M_fix i 0 a b t);
          nm_overlap_array_sep_3 sho sha shb o a b v_o v_a v_b k)).

Definition M1_inner_Inv sho sha shb v_o v_a v_b v_t i aux1 o a b t k :=
  EX j : Z,
   PROP  (
(*           writable_share sho; writable_share sha; writable_share shb;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_a;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_b;
          Zlength contents_a = 16;
          Zlength contents_b = 16;
          Zlength contents_o = 16;
          Zlength contents_t = 31; *)
(*           j >= 0 *)
          )
   LOCAL (temp _i (Vint (Int.repr i)); temp _aux aux1; lvar _t (tarray tlg 31) v_t;
    temp _a v_a; temp _b v_b; temp _o v_o)
   SEP   (
          Tsh [{ v_t }] <<(tarray tlg 31)-- mVI64 (outer_M_fix i j a b t);
          nm_overlap_array_sep_3 sho sha shb o a b v_o v_a v_b k).

(* Definition M2_Inv sho sha shb o a b t contents_o contents_a contents_b contents_t k :=
  EX i : Z,
   PROP  (
(*           writable_share sho; writable_share sha; writable_share shb;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_a;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_b;
          Zlength contents_a = 16;
          Zlength contents_b = 16;
          Zlength contents_o = 16;
          Zlength contents_t = 31;
          i >= 0
 *)
          )
   LOCAL (lvar _t (tarray tlg 31) t; temp _a a; temp _b b; temp _o o)
   SEP   (
          Tsh [{ t }] <<(tarray tlg 31)-- mVI64 (M2_fix i contents_t);
          nm_overlap_array_sep_3s sho sha shb contents_o contents_a contents_b o a b). *)

Definition M2_Inv F L v_t t :=
  EX i : Z,
   PROP  (
(*           writable_share sho; writable_share sha; writable_share shb;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_a;
          Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_b;
          Zlength contents_a = 16;
          Zlength contents_b = 16;
          Zlength contents_o = 16;
          Zlength contents_t = 31;
          i >= 0
 *)
          )
   (LOCALx L
   SEP   (FRZL F ;
(*    LOCAL (lvar _t (tarray tlg 31) t; temp _a a; temp _b b; temp _o o)
   SEP   (F
 *)
           Tsh [{ v_t }] <<(tarray tlg 31)-- mVI64 (M2_fix i t))).

Definition M3_Inv sho sha shb o a b t contents_o contents_a contents_b contents_t k :=
  EX i : Z,
   PROP  (
(*           writable_share sho; writable_share sha; writable_share shb; *)
(*           Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_a; *)
(*           Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) contents_b; *)
(*           Zlength contents_a = 16; *)
(*           Zlength contents_b = 16; *)
(*           Zlength contents_o = 16; *)
(*           Zlength contents_t = 31; *)
(*           i >= 0 *)
          )
   LOCAL (lvar _t (tarray tlg 31) t; temp _a a; temp _b b; temp _o o)
   SEP   (
          Tsh [{ t }] <<(tarray tlg 31)-- mVI64 contents_t;
          nm_overlap_array_sep_3' sho sha shb (M3_fix val i (mVI64 contents_t) contents_o) (mVI64 contents_a) (mVI64 contents_b) o a b k).

Close Scope Z.