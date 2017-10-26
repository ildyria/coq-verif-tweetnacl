Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.

Require Import stdpp.prelude.

(*
sv pack25519(u8 *o,const gf n)
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

