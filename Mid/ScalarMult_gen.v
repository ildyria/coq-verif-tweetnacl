Require Import ssreflect.
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
Require Import Tweetnacl.Gen.AMZubSqSel.

Section ScalarRec.

Context {O : Ops Z}.

Fixpoint montgomery_rec_gen (m : nat) (z a b c d e f x : Z) : (Z * Z * Z * Z * Z * Z) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat n) z in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      let e := A a c in
      let a := Zub a c in
      let c := A b d in
      let b := Zub b d in
      let d := Sq e in
      let f := Sq a in
      let a := M c a in
      let c := M b e in
      let e := A a c in
      let a := Zub a c in
      let b := Sq a in
      let c := Zub d f in
      let a := M c _121665 in
      let a := A a d in
      let c := M c a in
      let a := M d f in
      let d := M b x in
      let b := Sq e in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      montgomery_rec_gen n z a b c d e f x
    end.

Definition montgomery_step_gen (m:nat) (z a b c d e f x : Z) : (Z * Z * Z * Z * Z * Z)  :=
      let r := getbit (Z.of_nat m) z in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      let e := A a c in
      let a := Zub a c in
      let c := A b d in
      let b := Zub b d in
      let d := Sq e in
      let f := Sq a in
      let a := M c a in
      let c := M b e in
      let e := A a c in
      let a := Zub a c in
      let b := Sq a in
      let c := Zub d f in
      let a := M c _121665 in
      let a := A a d in
      let c := M c a in
      let a := M d f in
      let d := M b x in
      let b := Sq e in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      (a,b,c,d,e,f).
(*     end. *)

Lemma opt_montgomery_rec_step_gen : forall n z a b c d e f x,
  montgomery_rec_gen (S n) z a b c d e f x = 
  montgomery_rec_gen n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof. reflexivity. Qed.

Lemma opt_montgomery_rec_step_gen_ext : forall n z a b c d e f e' f' x,
  montgomery_rec_gen (S n) z a b c d e' f' x = 
  montgomery_rec_gen n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof. reflexivity. Qed.

End ScalarRec.
