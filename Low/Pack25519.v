From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Mid.SubList.
From stdpp Require Import prelude.
Require Import Recdef.

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
(*
0xffff = 65535
0xffed = 65517
0x7fff = 32767
*)

Definition subst_0xffed t := t - 65517.
Definition subst_0xffff t m := t - 65535 - (Z.land (Z.shiftr m 16) 1).
Definition subst_0x7fff t m := t - 32767 - (Z.land (Z.shiftr m 16) 1).
Definition mod0xffff m := Z.land m 65535.
Definition getBit256 l := Z.land (Z.shiftr (nth 15%nat l 0) 16) 1.

Definition step_sub (a:Z) (m t:list Z) : list Z :=
    let m' := nth (Z.to_nat (a - 1)) m 0 in
    let t' := nth (Z.to_nat a) t 0 in
      upd_nth (Z.to_nat (a-1)) (upd_nth (Z.to_nat a) m (subst_0xffff t' m')) (mod0xffff m').

Function sub_fn_rev (a:Z) (m t: list Z) {measure Z.to_nat a} : (list Z) :=
  if (a <=? 0)
    then m
    else
      let prev := sub_fn_rev (a - 1) m t in 
        step_sub a prev t.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma sub_fn_rev_0 : forall m t,
  sub_fn_rev 0 m t = m.
Proof. go. Qed.

Lemma sub_fn_rev_n : forall a m t,
  0 < a ->
  sub_fn_rev a m t = step_sub a (sub_fn_rev (a - 1) m t) t.
Proof. intros. rewrite sub_fn_rev_equation.
flatten ; apply Zle_bool_imp_le in Eq; omega.
Qed.

Definition m_from_t (m t:list Z) : list Z := 
  let m0 := upd_nth 0 m (subst_0xffed (nth 0 t 0)) in
  let m14 := sub_fn_rev 14 m0 t in
  let m15 := upd_nth 15 m14 (subst_0x7fff (nth 15 t 0) (nth 14 m14 0)) in
  upd_nth 14 m15 (mod0xffff (nth 14 m15 0)).

(*
Definition list25519 := [65517;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;65535;32767].
Lemma list_of_P: forall l,
  l = list25519 ->
  (ZofList 16 l) = Z.pow 2 255 - 19.
Proof. intros; subst; compute ; reflexivity. Qed.
*)





Close Scope Z.