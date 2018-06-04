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

Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Mid.Reduce.
Require Import Tweetnacl.Mid.GetBit.
Require Import Tweetnacl.Mid.ScalarMult_rev_fn_gen.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Gen.ABCDEF.

Open Scope Z.

(* Definition Zmontgomery_fn := Zabstract_fn_rev Zfa Zfb Zfc Zfd Zfe Zff Zgetbit.

Lemma Zmontgomery_fn_equation: forall (m p : ℤ) (z a b c d e f x : ℤ),
       Zmontgomery_fn m p z a b c d e f x =
       (if m <=? 0
        then (a, b, c, d, e, f)
        else
         let (p0, f0) := Zmontgomery_fn (m - 1) p z a b c d e f x in
         let (p1, e0) := p0 in
         let (p2, d0) := p1 in
         let (p3, c0) := p2 in
         let (a0, b0) := p3 in
         (Zfa (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, Zfb (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         Zfc (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, Zfd (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         Zfe (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, Zff (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x)).
Proof. apply Zabstract_fn_rev_equation. Qed.

Lemma Zmontgomery_fn_0 : forall p z a b c d e f x,
  Zmontgomery_fn 0 p z a b c d e f x = (a,b,c,d,e,f).
Proof. apply Zabstract_fn_rev_0. Qed.

Lemma Zmontgomery_fn_n : forall (m p : ℤ) (z a b c d e f x : ℤ),
       0 < m ->
       Zmontgomery_fn m p z a b c d e f x =
         let (p0, f0) := Zmontgomery_fn (m - 1) p z a b c d e f x in
         let (p1, e0) := p0 in
         let (p2, d0) := p1 in
         let (p3, c0) := p2 in
         let (a0, b0) := p3 in
         (Zfa (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, Zfb (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         Zfc (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, Zfd (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         Zfe (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, Zff (Zgetbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x).
Proof. apply Zabstract_fn_rev_n. Qed. *)

Close Scope Z.