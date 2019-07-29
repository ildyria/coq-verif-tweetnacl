Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.

Open Scope Z.

Definition set25519_spec := 
 DECLARE _set25519
  WITH r: val, a: val, shr : share, sha : share, contents_r : list val, contents_a : list Z
  PRE [ _r OF (tptr tlg), _a OF (tptr tlg)]
        PROP  (writable_share shr;
               readable_share sha;
                Zlength contents_a = 16;
                Zlength contents_r = 16)
        LOCAL (temp _r r; temp _a a)
        SEP   (sha [{ a }] <<(lg16)-- mVI64 contents_a;
               shr [{ r }] <<(lg16)-- contents_r)
  POST [ tvoid ]
        PROP ()
        LOCAL()
        SEP ( sha [{ a }] <<(lg16)-- mVI64 contents_a;
              shr [{ r }] <<(lg16)-- mVI64 contents_a).

Definition set25519_Inv shr sha r a contents_r contents_a := 
  EX i : Z,
   PROP  (writable_share shr; readable_share sha;
          Zlength contents_a = 16;
          Zlength contents_r = 16;
          i >= 0)
   LOCAL (temp _a a; temp _r r)
   SEP   (shr [{ r }] <<(lg16)-- ((list.take (nat_of_Z i) (mVI64 contents_a)) ++ list.drop (nat_of_Z i) contents_r);
          sha [{ a }] <<(lg16)-- mVI64 contents_a).

Close Scope Z.