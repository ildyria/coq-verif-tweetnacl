Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Low.S.

Open Scope Z.

Import Low.

Definition S_spec :=
 DECLARE _S
  WITH v_o: val, v_a: val, sho : share, sha : share, o : list val, a : list Z, k :Z
  PRE [ _o OF (tptr tlg), _a OF (tptr tlg) ]
        PROP  (writable_share sho; readable_share sha;
                Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a;
                Zlength a = 16;
                Zlength o = 16)
        LOCAL (temp _a v_a; temp _o v_o)
        SEP   (nm_overlap_array_sep_2 sho sha o (mVI64 a) v_o v_a k)
  POST [ tvoid ]
        PROP (
          Zlength (Low.S a) = 16;
          Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Low.S a))
        LOCAL()
        SEP (nm_overlap_array_sep_2' sho sha (mVI64 (S a)) (mVI64 a) v_o v_a k).

Close Scope Z.