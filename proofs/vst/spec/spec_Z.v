Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Low.Z.

Open Scope Z.

Definition Z_spec :=
 DECLARE _Z
  WITH v_o: val, v_a: val, v_b: val,
    sho : share, sha : share, shb : share,
    o : list val,
    a : list Z, amin : Z, amax : Z,
    b : list Z, bmin : Z, bmax : Z,
    k : Z
  PRE [ _o OF (tptr tlg), _a OF (tptr tlg), _b OF (tptr tlg) ]
        PROP  (writable_share sho; readable_share sha; readable_share shb;
                Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) a;
                Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) b;
                Forall (fun x => amin < x < amax) a;
                Forall (fun x => bmin < x < bmax) b;
                Zlength a = 16;
                Zlength b = 16;
                Zlength o = 16)
        LOCAL (temp _a v_a; temp _b v_b; temp _o v_o)
        SEP   (nm_overlap_array_sep_3 sho sha shb o a b v_o v_a v_b k)
  POST [ tvoid ]
        PROP (
              Forall (fun x => amin - bmax < x < amax - bmin) (Low.Z a b))
        LOCAL()
        SEP (nm_overlap_array_sep_3' sho sha shb (mVI64 (Low.Z a b)) (mVI64 a) (mVI64 b) v_o v_a v_b k).

Definition Z_Inv sho sha shb v_o v_a v_b o (a:list Z) amin amax (b:list Z) bmin bmax k := 
  EX i : Z,
   PROP  (writable_share sho; readable_share sha; readable_share shb;
          Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) a;
          Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) b;
          Forall (fun x => amin < x < amax) a;
          Forall (fun x => bmin < x < bmax) b;
          Zlength a = 16;
          Zlength b = 16;
          Zlength o = 16;
          i >= 0)
   LOCAL (temp _a v_a; temp _b v_b; temp _o v_o)
   SEP   (nm_overlap_array_sep_3' sho sha shb (tkdp i (mVI64 (Low.Z a b)) o) (mVI64 a) (mVI64 b) v_o v_a v_b k).

Close Scope Z.