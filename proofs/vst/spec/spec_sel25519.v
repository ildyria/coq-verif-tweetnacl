Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Low.Sel25519.
Require Import Tweetnacl.Low.Binary_select.

(*
sv sel25519(gf p,gf q,int b)
{
  i64 t,i,c=~(b-1);
  FOR(i,16) {
    t= c&(p[i]^q[i]);
    p[i]^=t;
    q[i]^=t;
  }
}
*)

Open Scope Z.

Import Low.

Definition sel25519_spec := 
 DECLARE _sel25519
  WITH p: val, q: val, sh : share, contents_p : list Z, contents_q : list Z, b:Z
  PRE [ _p OF (tptr tlg), _q OF (tptr tlg), _b OF tint]
        PROP  (writable_share sh;
                Zlength contents_p = 16;
                Zlength contents_q = 16;
                b = 0 \/ b = 1)
        LOCAL (temp _p p; temp _q q; temp _b (Vint (Int.repr b)))
        SEP   ( sh [{ p }] <<(lg16)-- mVI64 contents_p;
                sh [{ q }] <<(lg16)-- mVI64 contents_q)
  POST [ tvoid ]
        PROP ()
        LOCAL()
        SEP  (sh [{ p }] <<(lg16)-- mVI64 (Sel25519 b contents_p contents_q);
              sh [{ q }] <<(lg16)-- mVI64 (Sel25519 b contents_q contents_p)).

Definition sel25519_Inv sh p q b c contents_p contents_q := 
  EX i : Z,
    PROP  (writable_share sh;
            Zlength contents_p = 16;
            Zlength contents_q = 16;
            b = 0 \/ b = 1;
            c = set_xor b)
    LOCAL (temp _c (Vlong (Int64.repr c)); temp _p p; temp _q q; temp _b (Vint (Int.repr b)))
    SEP   ( sh [{ p }] <<(lg16)-- mVI64 (list.take (nat_of_Z i) (Sel25519 b contents_p contents_q) ++ list.drop (nat_of_Z i) contents_p);
            sh [{ q }] <<(lg16)-- mVI64 (list.take (nat_of_Z i) (Sel25519 b contents_q contents_p) ++ list.drop (nat_of_Z i) contents_q)).

Close Scope Z.