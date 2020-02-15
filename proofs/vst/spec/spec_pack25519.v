(*sv pack25519(u8 *o,const gf n)
{
  int i,j,b;
  gf m,t;
  FOR(i,16) t[i]=n[i];
  car25519(t);
  car25519(t);
  car25519(t);
  FOR(j,2) {
    m[0]=t[0]- (i64)0xffed;
    for(i=1;i<15;i++) {
      m[i]=t[i]- (i64)0xffff-((m[i-1]>>16)& (i64)1);
      m[i-1]&= (i64)0xffff;
    }
    m[15]=t[15]- (i64)0x7fff-((m[14]>>16)& (i64)1);
    b=(m[15]>>16)& (i64)1;
    m[14]&= (i64)0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]& (unsigned char) 0xff;
    o[2*i+1]=t[i]>>8;
  }
}
*)

Set Warnings "-notation-overridden,-parsing".
From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Low Require Import Get_abcdef.
From Tweetnacl.Low Require Import Reduce_by_P.
From Tweetnacl.Low Require Import Reduce_by_P_compose_step.
From Tweetnacl.Low Require Import Pack.
From Tweetnacl.Low Require Import GetBit_pack25519.
From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Car25519.
From Tweetnacl_verif Require Import init_tweetnacl.

Open Scope Z.

Definition pack25519_spec := 
 DECLARE _pack25519
  WITH o: val, n: val, sh : share, tsh : share, contents_o : list val, contents_n : list Z
  PRE [ _o OF (tptr tuchar), _n OF (tptr tlg)]
        PROP  ( writable_share tsh; readable_share sh;
                Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) contents_n;
                Zlength contents_n = 16;
                Zlength contents_o = 32)
        LOCAL (temp _o o; temp _n n)
        SEP   (  sh [{ n }] <<(lg16)-- mVI64 contents_n;
                tsh [{ o }] <<(uch32)-- contents_o)
  POST [ tvoid ]
        PROP (Forall (fun x => 0 <= x < Z.pow 2 8) (Pack25519 contents_n))
        LOCAL()
        SEP   (  sh [{ n }] <<(lg16)-- mVI64 contents_n;
                tsh [{ o }] <<(uch32)-- mVI (Pack25519 contents_n)).

Definition pack25519_Sub F (L:list localdef) sh v_t v_m t m := 
  EX j : Z,
   PROP  (writable_share sh;
          Zlength m = 16;
          Zlength t = 16;
          j >= 0)
   (LOCALx L
   SEP   (FRZL F;
          data_at sh (tarray tlg 16) (mVI64 (get_t (subst_select select_m_t j m t))) v_t;
          data_at sh (tarray tlg 16) (mVI64 (get_m (subst_select select_m_t j m t))) v_m)).

Definition pack25519_Sub_Step F (L:list localdef) sh v_t v_m t m := 
  EX j : Z,
   PROP  (writable_share sh;
          Zlength m = 16;
          Zlength t = 16;
          j >= 1)
   (LOCALx L
   SEP   (FRZL F;
          data_at sh (tarray tlg 16) (mVI64 t) v_t;
          data_at sh (tarray tlg 16) (mVI64 (sub_fn_rev 1 sub_step j m t)) v_m)).

Definition pack25519_pack_for F (L:list localdef) sh tsh v_o v_m o m := 
  EX i : Z,
   PROP  (readable_share sh;
          writable_share tsh; 
          i >= 0)
   (LOCALx L
   SEP   (FRZL F; 
          sh [{ v_m }] <<(lg16)-- mVI64 m ;
          tsh [{ v_o }] <<(uch32)-- ((list.take (nat_of_Z (2 * i)) (mVI (pack_for 8 m)) ++ list.drop (nat_of_Z (2 * i)) o)))).

Close Scope Z.