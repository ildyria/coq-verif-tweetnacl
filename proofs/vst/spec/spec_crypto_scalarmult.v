(*
int crypto_scalarmult(u8 *q,const u8 *n,const u8 *p)
{
  u8 z[32];
  i64 x[80],r;
  int i;
  gf a,b,c,d,e,f;
  FOR(i,31) z[i]=n[i];
  z[31]=(n[31]&127)|64;
  z[0]&=248;
  unpack25519(x,p);
  FOR(i,16) {
    b[i]=x[i];
    d[i]=a[i]=c[i]=0;
  }
  a[0]=d[0]=1;
  for(i=254;i>=0;--i) {
    r=(z[i>>3]>>(i&7))&1;
    sel25519(a,b,r);
    sel25519(c,d,r);
    A(e,a,c);
    Z(a,a,c);
    A(c,b,d);
    Z(b,b,d);
    S(d,e);
    S(f,a);
    M(a,c,a);
    M(c,b,e);
    A(e,a,c);
    Z(a,a,c);
    S(b,a);
    Z(c,d,f);
    M(a,c,_121665);
    A(a,a,d);
    M(c,c,a);
    M(a,d,f);
    M(d,b,x);
    S(b,e);
    sel25519(a,b,r);
    sel25519(c,d,r);
  }
  FOR(i,16) {
    x[i+16]=a[i];
    x[i+32]=c[i];
    x[i+48]=b[i];
    x[i+64]=d[i];
  }
  inv25519(x+32,x+32);
  M(x+16,x+16,x+32);
  pack25519(q,x+16);
  return 0;
}
*)

Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl_verif.spec_sel25519.
Require Import Tweetnacl_verif.spec_unpack25519.
Require Import Tweetnacl_verif.spec_pack25519.
Require Import Tweetnacl_verif.spec_inv25519.
Require Import Tweetnacl_verif.spec_A.
Require Import Tweetnacl_verif.spec_Z.
Require Import Tweetnacl_verif.spec_S.
Require Import Tweetnacl_verif.spec_M.
Require Import Tweetnacl_verif.verif_crypto_scalarmult_lemmas.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_rev.
Require Import Tweetnacl.Low.Constant.
(* Require Import Tweetnacl.Low.Crypto_Scalarmult. *)
(* Require Import Tweetnacl.Low.Crypto_Scalarmult_. *)
Require Import Tweetnacl.Mid.Instances.
Require Import Tweetnacl.rfc.rfc.
Open Scope Z.

Import Low.

Definition crypto_scalarmult_spec :=
 DECLARE _crypto_scalarmult_curve25519_tweet
  WITH 
    v_q: val, v_n: val, v_p: val, c121665:val,
    sh : share,
    q : list val, 
    n : list Z,
    p : list Z
 PRE [ _q OF (tptr tuchar),
       _n OF (tptr tuchar), _p OF (tptr tuchar) ]
        PROP  (writable_share sh;
                Forall (fun x => 0 <= x < Z.pow 2 8) p;
                Forall (fun x => 0 <= x < Z.pow 2 8) n;
                Zlength q = 32;
                Zlength n = 32;
                Zlength p = 32)
        LOCAL(temp _q v_q; temp _n v_n; temp _p v_p; gvar __121665 c121665)
        SEP  (sh [{ v_q }] <<(uch32)-- q;
              sh [{ v_n }] <<(uch32)-- mVI n;
              sh [{ v_p }] <<(uch32)-- mVI p;
              Ews [{ c121665 }] <<(lg16)-- mVI64 C_121665)
  POST [ tint ]
        PROP (
                Forall (fun x => 0 <= x < Z.pow 2 8) (RFC n p);
                Zlength (RFC n p) = 32)
        LOCAL(temp ret_temp (Vint Int.zero))
        SEP (sh [{ v_q }] <<(uch32)-- mVI (RFC n p);
              sh [{ v_n }] <<(uch32)-- mVI n;
              sh [{ v_p }] <<(uch32)-- mVI p;
              Ews [{ c121665 }] <<(lg16)-- mVI64 C_121665
        ).

Definition crypto_scalarmult_Zinit_Inv F (L:list localdef) sh v_z n (contents_n:list Z) := 
  EX i : Z,
   PROP  (writable_share sh;
          Forall (fun x => 0 <= x < Z.pow 2 8) contents_n;
          Zlength contents_n = 32;
          i >= 0)
   (LOCALx L
   SEP   (FRZL F;
          Tsh [{ v_z }] <<(uch32)-- (list.take (nat_of_Z i) (map Vint (map Int.repr contents_n)) ++ list.drop (nat_of_Z i) undef32);
           sh [{  n  }] <<(uch32)-- mVI contents_n
          )).

Definition crypto_scalarmult_BDACinit_Inv F L sh v_x v_a v_b v_c v_d contents_x := 
  EX i : Z,
   PROP  (writable_share sh;
          Forall (fun x => 0 <= x < Z.pow 2 16) contents_x;
          Zlength contents_x = 16;
          i >= 0)
   (LOCALx L
   SEP   (FRZL F;
          Tsh [{ v_b }] <<(lg16)-- (list.take (nat_of_Z i) (mVI64 contents_x) ++ list.drop (nat_of_Z i) undef16) ;
          Tsh [{ v_a }] <<(lg16)-- (list.take (nat_of_Z i) (mVI64 nil16) ++ list.drop (nat_of_Z i) undef16) ;
          Tsh [{ v_c }] <<(lg16)-- (list.take (nat_of_Z i) (mVI64 nil16) ++ list.drop (nat_of_Z i) undef16) ;
          Tsh [{ v_d }] <<(lg16)-- (list.take (nat_of_Z i) (mVI64 nil16) ++ list.drop (nat_of_Z i) undef16) ;
          Tsh [{ v_x }] <<(lg16)-- mVI64 contents_x)).

Definition crypto_scalarmult_ladder_Inv F sh v_z v_x v_a v_b v_c v_d v_e v_f q z a b c d x c121665 :=
(* Loop Invariant *)
fun i:Z => 
  PROP (
    writable_share sh;
    Forall (fun x => 0 <= x < Z.pow 2 8) z;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) a;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) b;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) d;
    Forall (fun x => 0 <= x < Z.pow 2 16) x;
    Zlength z = 32;
    Zlength a = 16;
    Zlength b = 16;
    Zlength c = 16;
    Zlength d = 16;
    Zlength x = 16;
    -1 <= i <= 254
    )
  LOCAL ( (temp _i (Vint (Int.repr i))) ;
      lvar _f (tarray tlg 16) v_f; lvar _e (tarray tlg 16) v_e; lvar _d (tarray tlg 16) v_d;
      lvar _c (tarray tlg 16) v_c; lvar _b (tarray tlg 16) v_b; lvar _a (tarray tlg 16) v_a;
      lvar _x (tarray tlg 16) v_x; lvar _z (tarray tuchar 32) v_z; temp _q q;
      gvar __121665 c121665)
  SEP (FRZL F;
    Tsh [{ v_z }] <<(uch32)-- (map Vint (map Int.repr z));
    Tsh [{ v_a }] <<(lg16)-- (mVI64 (get_a (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_b }] <<(lg16)-- (mVI64 (get_b (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_c }] <<(lg16)-- (mVI64 (get_c (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_d }] <<(lg16)-- (mVI64 (get_d (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) ;
    set_undef_array_sep Tsh 254 i (mVI64 (get_e (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) v_e;
    set_undef_array_sep Tsh 254 i (mVI64 (get_f (montgomery_fn List_Z_Ops (254 - i) 254 z a b c d nil16 nil16 x))) v_f;
    Tsh [{ v_x }] <<(lg16)-- mVI64 x;
    Ews [{ c121665 }] <<(lg16)-- (mVI64 C_121665)).

Definition crypto_scalarmult_ladder_PreIncInv F sh v_z v_x v_a v_b v_c v_d v_e v_f q z a b c d x c121665 :=
(* PreDec invariant *)
  fun i:Z =>
  PROP (
    writable_share sh;
    Forall (fun x => 0 <= x < Z.pow 2 8) z;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) a;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) b;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) d;
    Forall (fun x => 0 <= x < Z.pow 2 16) x;
    Zlength z = 32;
    Zlength a = 16;
    Zlength b = 16;
    Zlength c = 16;
    Zlength d = 16;
    Zlength x = 16;
    0 <= i <= 254
   )
  LOCAL ((temp _i (Vint (Int.repr i)));
      lvar _f (tarray tlg 16) v_f; lvar _e (tarray tlg 16) v_e; lvar _d (tarray tlg 16) v_d;
      lvar _c (tarray tlg 16) v_c; lvar _b (tarray tlg 16) v_b; lvar _a (tarray tlg 16) v_a;
      lvar _x (tarray tlg 16) v_x; lvar _z (tarray tuchar 32) v_z; temp _q q;
      gvar __121665 c121665)
   SEP (FRZL F;
    Tsh [{ v_z }] <<(uch32)-- (map Vint (map Int.repr z));
    Tsh [{ v_a }] <<(lg16)-- (mVI64 (get_a (montgomery_fn List_Z_Ops (254 - (i - 1)) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_b }] <<(lg16)-- (mVI64 (get_b (montgomery_fn List_Z_Ops (254 - (i - 1)) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_c }] <<(lg16)-- (mVI64 (get_c (montgomery_fn List_Z_Ops (254 - (i - 1)) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_d }] <<(lg16)-- (mVI64 (get_d (montgomery_fn List_Z_Ops (254 - (i - 1)) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_e }] <<(lg16)-- (mVI64 (get_e (montgomery_fn List_Z_Ops (254 - (i - 1)) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_f }] <<(lg16)-- (mVI64 (get_f (montgomery_fn List_Z_Ops (254 - (i - 1)) 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_x }] <<(lg16)-- mVI64 x;
    Ews [{ c121665 }] <<(lg16)-- (mVI64 C_121665)).

Definition crypto_scalarmult_ladder_PostInv F sh v_z v_x v_a v_b v_c v_d v_e v_f q z a b c d x c121665 :=
(* Loop postcondition *)
 PROP (
    writable_share sh;
    Forall (fun x => 0 <= x < Z.pow 2 8) z;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) a;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) b;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c;
    Forall (fun x => -38 <= x < Z.pow 2 16 + 38) d;
    Forall (fun x => 0 <= x < Z.pow 2 16) x;
    Zlength z = 32;
    Zlength a = 16;
    Zlength b = 16;
    Zlength c = 16;
    Zlength d = 16;
    Zlength x = 16
  )
 LOCAL (
      lvar _f (tarray tlg 16) v_f; lvar _e (tarray tlg 16) v_e; lvar _d (tarray tlg 16) v_d;
      lvar _c (tarray tlg 16) v_c; lvar _b (tarray tlg 16) v_b; lvar _a (tarray tlg 16) v_a;
      lvar _x (tarray tlg 16) v_x; lvar _z (tarray tuchar 32) v_z; temp _q q;
      gvar __121665 c121665)
   SEP (FRZL F;
    Tsh [{ v_z }] <<(uch32)-- (map Vint (map Int.repr z));
    Tsh [{ v_a }] <<(lg16)-- (mVI64 (get_a (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_b }] <<(lg16)-- (mVI64 (get_b (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_c }] <<(lg16)-- (mVI64 (get_c (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_d }] <<(lg16)-- (mVI64 (get_d (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_e }] <<(lg16)-- (mVI64 (get_e (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_f }] <<(lg16)-- (mVI64 (get_f (montgomery_fn List_Z_Ops 255 254 z a b c d nil16 nil16 x))) ;
    Tsh [{ v_x }] <<(lg16)-- mVI64 x;
    Ews [{ c121665 }] <<(lg16)-- (mVI64 C_121665)).
