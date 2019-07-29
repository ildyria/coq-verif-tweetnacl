Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Low.Unpack25519.
Require Import Tweetnacl_verif.init_tweetnacl.

(*
sv unpack25519(gf o, const u8 *n)
{
  int i;
  FOR(i,16) o[i]=n[2*i]+((i64)n[2*i+1]<<8);
  o[15]&= (i64) 0x7fff;
}
*)

Open Scope Z.

Definition unpack25519_spec := 
 DECLARE _unpack25519
  WITH o: val, n: val, sh : share, tsh : share, contents_o : list val, contents_n : list Z
  PRE [ _o OF (tptr tlg), _n OF (tptr tuchar)]
        PROP  (writable_share tsh; readable_share sh;
                Forall (fun x => 0 <= x < Z.pow 2 8) contents_n;
                Zlength contents_n = 32;
                Zlength contents_o = 16)
        LOCAL (temp _o o; temp _n n)
        SEP   (  sh [{ n }] <<(uch32)-- mVI contents_n;
                tsh [{ o }] <<(lg16)-- contents_o)
  POST [ tvoid ]
        PROP (Forall (fun x => 0 <= x < Z.pow 2 16) (Unpack25519 contents_n))
        LOCAL()
        SEP   (  sh [{ n }] <<(uch32)-- mVI contents_n;
                tsh [{ o }] <<(lg16)--  mVI64 (Unpack25519 contents_n)).

Definition unpack25519_Inv sh tsh o n (contents_o:list val) (contents_n:list Z) := 
  EX i : Z,
   PROP  (writable_share tsh; readable_share sh;
          Forall (fun x => 0 <= x < Z.pow 2 8) contents_n;
          Zlength contents_n = 32;
          Zlength contents_o = 16;
          i >= 0)
   LOCAL (temp _o o; temp _n n)
   SEP   ( sh [{ n }] <<(uch32)-- mVI contents_n;
          tsh [{ o }] <<(lg16)--  (mVI64 (list.take (nat_of_Z i) (unpack_for 8 contents_n)) ++ (list.drop (nat_of_Z i) contents_o))).

Close Scope Z.