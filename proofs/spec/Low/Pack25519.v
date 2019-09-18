From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P.
From Tweetnacl Require Import Low.Car25519.
From Tweetnacl Require Import Low.Car25519_bounds.
From Tweetnacl Require Import Low.Get_abcdef.
From Tweetnacl Require Import Low.Pack.
From Tweetnacl Require Import Mid.Pack25519.
Require Import ssreflect.
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
    m[0]=t[0]-0xffed;

    for(i=1;i<15;i++) {
      m[i]=t[i]-0xffff-((m[i-1]>>16)&1);
      m[i-1]&=0xffff;
    }

    m[15]=t[15]-0x7fff-((m[14]>>16)&1);
    b=(m[15]>>16)&1;
    m[14]&=0xffff;
    sel25519(t,m,1-b);
  }
  FOR(i,16) {
    o[2*i]=t[i]&0xff;
    o[2*i+1]=t[i]>>8;
  }
}
*)

Open Scope Z.

Definition Pack25519 l :=
  let l1 := car25519 l in
  let l2 := car25519 l1 in
  let l3 := car25519 l2 in
  let l4 := get_t (subst_select select_m_t 2 (0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::0::nil) l3) in
  pack_for 8 l4.

Lemma Pack25519_mod_25519 : forall (l:list Z),
  Zlength l = 16 ->
  Forall (fun x => -2^62 < x < 2^62) l ->
  ZofList 8 (Pack25519 l) = ZPack25519 (ZofList 16 l).
Proof.
  intros l Hl Hb.
  rewrite /Pack25519 /ZPack25519.
  rewrite pack_for_correct.
  2: omega.
  change (2*8) with 16.
  rewrite subst_select_mod_P.
  repeat rewrite -car25519_ToFF_25519 ; repeat rewrite car25519_Zlength ; try reflexivity ; assumption.
  reflexivity.
  repeat rewrite car25519_Zlength ; try reflexivity ; assumption.
  apply car25519_bound ; assumption.
Qed.

Lemma Pack25519_bound : forall (l:list Z),
  Zlength l = 16 ->
  Forall (fun x => -2^62 < x < 2^62) l ->
  Forall (fun x => 0 <= x < 2^8) (Pack25519 l).
Proof.
  intros l Hl Hb.
  rewrite /Pack25519.
  apply unpack_for_bounded.
  apply get_t_subst_select_bound.
  omega.
  reflexivity.
  repeat rewrite car25519_Zlength ; try reflexivity ; assumption.
  apply car25519_bound ; assumption.
Qed.

Lemma Pack25519_Zlength : forall (l:list Z),
  Zlength l = 16 ->
  Zlength (Pack25519 l) = 32.
Proof.
  move => l Hl.
  rewrite /Pack25519.
  apply Pack.pack_for_Zlength_32_16.
  apply Reduce_by_P.get_t_subst_select_Zlength => //=.
  do 3 apply car25519_Zlength => //.
Qed.

Close Scope Z.
