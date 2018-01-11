From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose.
From Tweetnacl Require Import Mid.SubList.
From Tweetnacl Require Import Low.Get_abcdef.
From Tweetnacl Require Import Low.GetBit_pack25519.
From Tweetnacl Require Import Low.Sel25519.
From Tweetnacl Require Import Low.Constant.
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

Definition getBit256 l := Z.land (Z.shiftr (nth 15%nat l 0) 16) 1.

Lemma nth_i_1_substep_bounds: forall i m t,
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  0 <= nth (Z.to_nat (i - 1)) (sub_step i m t) 0 < 2^16.
Proof.
  intros.
  rewrite nth_i_1_substep //.
  rewrite /mod0xffff.
  change 65535 with (Z.ones 16).
  rewrite Z.land_ones ; try omega.
  apply Z_mod_lt.
  apply pown0 ; omega.
Qed.

Lemma nth_i_substep_bounds: forall i m t,
  Zlength m = Zlength t ->
  0 < i < Zlength m ->
  Forall (fun x => 0 <= x < 2^16) t ->
  -2^16 <= nth (Z.to_nat i) (sub_step i m t) 0 <= 0.
Proof.
intros i m t Hmt Him HPt.
rewrite nth_i_substep //.
rewrite /subst_0xffffc.
assert(HP0: 0 ≤ 0 ∧ 0 < 2 ^ 16) by (split ; try omega ; apply Z.gt_lt ; apply pown0 ; omega).
assert(0 ≤ (nth (Z.to_nat i) t 0) ∧ (nth (Z.to_nat i) t 0) < 2 ^ 16).
apply Forall_nth_d; assumption.
assert(HZlandminmax:= and_0_or_1 (nth (Z.to_nat (i - 1)) m 0 ≫ 16)).
assert(HZland: Z.land (nth (Z.to_nat (i - 1)) m 0 ≫ 16) 1 = 0 \/ Z.land (nth (Z.to_nat (i - 1)) m 0 ≫ 16) 1 = 1) by omega.
destruct HZland as [HZland|HZland]; rewrite HZland.
all: change (2^16) with 65536 in * ; omega.
Qed.

Lemma subst_select_step_Zlength : forall i m t,
  0 < i < Zlength m->
  Zlength (sub_step i m t) = Zlength m.
Proof.
  intros.
  rewrite /sub_step.
  assert(0 < Z.to_nat i /\ Z.to_nat i < Zlength m) by (rewrite ?Z2Nat.id ; omega).
  assert(Z.of_nat (Z.to_nat (i - 1)) = (Z.of_nat (Z.to_nat i)) - 1) by (rewrite ?Z2Nat.id ; omega).
  rewrite ?upd_nth_Zlength ; omega.
Qed.

Definition m_from_t (m t:list Z) : list Z :=
  let m0 := upd_nth 0 m (subst_0xffed (nth 0 t 0)) in
  let m14 := sub_fn_rev sub_step 15 m0 t in
  let m15 := upd_nth 15 m14 (subst_0x7fffc (nth 15 t 0) (nth 14 m14 0)) in
  upd_nth 14 m15 (mod0xffff (nth 14 m15 0)).

Local Lemma m_from_t_dep_length : forall m m' t,
  (length m = 16)%nat ->
  (length m' = 16)%nat ->
  (length t = 16)%nat ->
  m_from_t m' t = m_from_t m t.
Proof.
  intros.
  do 17 (destruct m ; [tryfalse |]) ; [|tryfalse].
  do 17 (destruct m' ; [tryfalse |]) ; [|tryfalse].
  do 17 (destruct t ; [tryfalse |]) ; [|tryfalse].
  rewrite /m_from_t.
  simpl nth; simpl upd_nth.
  reflexivity.
Qed.

Lemma m_from_t_dep_Zlength : forall m m' t,
  Zlength m = 16 ->
  Zlength m' = 16 ->
  Zlength t = 16 ->
  m_from_t m' t = m_from_t m t.
Proof. convert_length_to_Zlength m_from_t_dep_length. Qed.

Lemma Zlandshift1 : forall a, (Z.land (a ≫ 16) 1) = Z.modulo (a / 2^16) 2.
Proof. intros. change 1 with (Z.ones 1) ; rewrite Z.shiftr_div_pow2 ?Z.land_ones ;  try omega.
reflexivity.
Qed.

(*
Lemma sub_step_ZofList : forall i t m,
  1 < i < Zlength t ->
  Zlength m = Zlength t ->
  ZofList 16 (sub_step i m t) = ZofList 16 m - (2*(16 *i) * nth (Z.to_nat i) m 0) + (2*(16 * i) * nth (Z.to_nat i) t 0) - (2^(16 * i) * 65535).
Proof.
intros.
rewrite /sub_step.

Lemma m_from_t_Z_of_list : forall t,
  (length t = 16)%nat ->
  ZofList 16 (m_from_t nul16 t) = ZofList 16 (ZsubList t list25519).
Proof.
intros t Ht; rewrite /nul16 /list25519.
do 17 (destruct t; [tryfalse|]) ; [|tryfalse].
simpl.
rewrite /subst_0xffed /mod0xffff.
change 65535 with (Z.ones 16).
rewrite ?Z.land_ones /subst_0xffff.
all: try omega.
assert(Hmodsub: forall a b c, (a - b - c) mod 2^16 = (((a - b) mod 2^16) - (c mod 2^16)) mod 2^16).
{ intros a b c ; rewrite Zminus_mod ; reflexivity. }
rewrite ?Hmodsub.
rewrite ?Zlandshift1.
assert(Hmultdist: forall a b,
2 ^ 16 *
((a `mod` 2 ^ 16 - ((b `div` 2 ^ 16) `mod` 2) `mod` 2 ^ 16) `mod` 2 ^ 16) =
(- (((b `div` 2 ^ 16) `mod` 2) `mod` 2 ^ 16) * 2 ^ 16 + 2^16 * (a `mod` 2 ^ 16  `mod` 2 ^ 16)) `mod` 2 ^ 16).
{ intros.
rewrite Z.mul_comm.
assert(2 ^ 16 > 0) by (apply pown0 ; omega).
rewrite -Z.mul_mod_distr_r ; try omega.
rewrite Z.mul_sub_distr_r.
rewrite -Z.add_opp_l.
Search Z.add Z.modulo.

 2^16 * (Z.modulo (a - b) 2^16) = - 2^16 * (Z.modulo b 2^16) + 2 ^ 16 * (Z.modulo a 2^16)).
{ intros.
 ; ring. }
rewrite ?Hmultdist.
*)

Local Lemma sub_fn_rev_Zlength_ind_step : forall i m t,
  0 < i < Zlength m ->
  Zlength (sub_fn_rev sub_step i m t) = Zlength m ->
  Zlength (sub_fn_rev sub_step (i+1) m t) = Zlength m.
Proof.
intros i m t Him Hind.
rewrite sub_fn_rev_equation.
flatten.
replace ( i + 1 - 1) with i by omega.
rewrite -Hind.
apply subst_select_step_Zlength.
rewrite Hind.
assumption.
Qed.

Lemma sub_fn_rev_Zlength : forall i m t,
  Zlength m = 16 ->
  0 < i < Zlength m ->
  Zlength (sub_fn_rev sub_step i m t) = Zlength m.
Proof.
intros.
change(Zlength (sub_fn_rev sub_step i m t) = Zlength m) with
  ((fun x => Zlength (sub_fn_rev sub_step x m t) = Zlength m) i).
apply P016_impl.
by rewrite sub_fn_rev_1.
intros ; apply sub_fn_rev_Zlength_ind_step.
2: apply H2.
all: omega.
Qed.

Definition select_m_t m t : (list Z * list Z) :=
  let new_m := m_from_t m t in 
  let b := 1 - getbit_25519 new_m in
    (Sel25519 b new_m t, Sel25519 b t new_m).

Lemma m_from_t_Zlength : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (m_from_t m t) = 16.
Proof.
  intros m t Hm Ht.
  rewrite /m_from_t.
  repeat match goal with 
    | _ => omega
    | _ => rewrite sub_fn_rev_Zlength
    | _ => rewrite upd_nth_Zlength
    | _ => change_Z_of_nat ; omega
  end.
Qed.

Lemma get_m_select_m_t_Zlength : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (get_m (select_m_t m t)) = 16.
Proof.
  intros m t Hm Ht;
  rewrite /select_m_t /get_m /get_t;
  apply Sel25519_Zlength ; try apply m_from_t_Zlength; assumption.
Qed.

Lemma get_t_select_m_t_Zlength : forall m t,
  Zlength m = 16 ->
  Zlength t = 16 ->
  Zlength (get_t (select_m_t m t)) = 16.
Proof.
  intros m t Hm Ht;
  rewrite /select_m_t /get_m /get_t;
  apply Sel25519_Zlength ; try apply m_from_t_Zlength; assumption.
Qed.


Function subst_select (f: list Z -> list Z -> list Z*list Z) (a:Z) (m t: list Z) {measure Z.to_nat a} : (list Z*list Z) :=
  if (a <=? 0)
    then (m,t)
    else
      let m_prev := get_m (subst_select f (a - 1) m t) in 
      let t_prev := get_t (subst_select f (a - 1) m t) in 
        (f m_prev t_prev).
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma subst_select_0 : forall f m t,
  subst_select f 0 m t = (m,t).
Proof. go. Qed.

Lemma subst_select_n : forall a m t f,
  0 < a ->
  subst_select f a m t = (f (get_m (subst_select f (a - 1) m t)) (get_t (subst_select f (a - 1) m t))).
Proof. intros. rewrite subst_select_equation.
flatten ; apply Zle_bool_imp_le in Eq; omega.
Qed.

Lemma get_m_subst_select_f_Zlength : forall i (m t:list Z) (f: list Z -> list Z -> list Z * list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_m (f m' t')) = 16) ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_t (f m' t')) = 16) ->
    Zlength (get_m (subst_select f i m t)) = 16.
Proof.
  intros i m t f Hi Hm Ht Hfm Hft.
  assert_gen_hyp i 2 2; [omega|].
  destruct H as [H|[H|H]] ; subst i;
  try solve [rewrite subst_select_n ; go] ; go.
Qed.

Lemma get_t_subst_select_f_Zlength : forall i (m t:list Z) (f: list Z -> list Z -> list Z * list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_m (f m' t')) = 16) ->
  (forall (m' t':list Z), Zlength m' = 16 -> Zlength t' = 16 -> Zlength (get_t (f m' t')) = 16) ->
    Zlength (get_t (subst_select f i m t)) = 16.
Proof.
  intros i m t f Hi Hm Ht Hfm Hft.
  assert_gen_hyp i 2 2; [omega|].
  destruct H as [H|[H|H]] ; subst i;
  try solve [rewrite subst_select_n ; go] ; go.
Qed.

Lemma get_m_subst_select_Zlength : forall i (m t:list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
    Zlength (get_m (subst_select select_m_t i m t)) = 16.
Proof.
  intros. apply get_m_subst_select_f_Zlength ; auto.
  apply get_m_select_m_t_Zlength.
  apply get_t_select_m_t_Zlength.
Qed.

Lemma get_t_subst_select_Zlength : forall i (m t:list Z),
  0 <= i <= 2->
  Zlength m = 16 ->
  Zlength t = 16 ->
    Zlength (get_t (subst_select select_m_t i m t)) = 16.
Proof.
  intros. apply get_t_subst_select_f_Zlength ; auto.
  apply get_m_select_m_t_Zlength.
  apply get_t_select_m_t_Zlength.
Qed.

Close Scope Z.