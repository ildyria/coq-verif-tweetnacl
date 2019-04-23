Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrbool eqtype div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import montgomery.
From Tweetnacl.High Require Import curve25519.
From Tweetnacl.High Require Import twist25519.
From Tweetnacl.High Require Import opt_ladder.
From Tweetnacl.High Require Import curve25519_prime.
From Tweetnacl.High Require Import prime_ssrprime.
From Reciprocity Require Import Reciprocity.Reciprocity.
From Tweetnacl.High Require Import Zmodp2.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_eq.
From Tweetnacl.High Require Import Zmodp.
Require Import Ring.
Require Import ZArith.

Import BinInt.

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "Z.R A" := (Zmodp.repr A) (at level 30).
Local Notation "-. A" := (Zmodp.opp A) (at level 30).

Local Lemma expr3 : forall x:Zmodp2.type, x^+3 = x*x*x :> Zmodp2.type.
Proof.
move => x; rewrite ?exprSr expr0 GRing.mul1r //.
Qed.

Local Lemma expr3' : forall x:Zmodp.type, (x^+3 = x*x*x)%R.
Proof.
move => x; rewrite ?exprSr expr0 GRing.mul1r //.
Qed.

Local Lemma oncurve_00 : (oncurve curve25519_Fp2_mcuType (EC_In 0 0)).
Proof.
  simpl; rewrite /a /b ; apply/eqP.
  have ->: (0 ^+ 2)%R = 0 :> Zmodp2.type by rewrite expr2 ?GRing.mulr0.
  have ->: (0 ^+ 3)%R = 0 :> Zmodp2.type by rewrite expr3 ?GRing.mulr0.
  rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
  f_equal; f_equal; apply/eqP ; zmodp_compute => //=.
Qed.

Local Lemma oncurve25519 : forall x k k0 : Zmodp.type,
curve25519.b * k0 ^+ 2 == k ^+ 3 + curve25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have OC: (oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (k, Zmodp.pi 0)) (Zmodp2.pi (k', Zmodp.pi 0)))) => /=.
rewrite /a /b.
rewrite ?expr2 ?expr3.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
move: Hx.
rewrite /curve25519.a /curve25519.b.
rewrite ?expr2 ?expr3'.
rewrite ?GRing.mul1r.
move/eqP.
move=> ->.
rewrite ?GRing.mul0r ?GRing.mulr0 ?GRing.addr0.
apply/eqP; f_equal ; f_equal.
rewrite /a /b.
exists (MC OC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Local Lemma ontwist25519 : forall x k k0 : Zmodp.type,
twist25519.b * k0 ^+ 2 == k ^+ 3 + twist25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have OC: (oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (k, Zmodp.pi 0)) (Zmodp2.pi (Zmodp.pi 0, k')))) => /=.
rewrite /a /b.
rewrite ?expr2 ?expr3.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
move: Hx.
rewrite /twist25519.b /twist25519.a.
rewrite ?expr2 ?expr3'.
rewrite ?GRing.mul1r.
move/eqP.
move=> ->.
rewrite ?GRing.mul0r ?GRing.mulr0 ?GRing.addr0 ?GRing.add0r.
apply/eqP; f_equal ; f_equal.
exists (MC OC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Lemma x_is_on_curve_or_twist_implies_x_in_Fp2: forall (x:Zmodp.type),
  exists (p: mc curve25519_Fp2_mcuType), p#x0 = Zmodp2.Zmodp2 x 0.
Proof.
  move=> x.
  have := x_is_on_curve_or_twist x.
  move=> [] [] [] [] /=.
  - move=> _ <- ; exists (MC oncurve_00) => //=.
  - apply oncurve25519.
  - move=> _ <- ; exists (MC oncurve_00) => //=.
  - apply ontwist25519.
Qed.

(* 
Lemma Zmodp2_ring : ring_theory Zmodp2.zero Zmodp2.one Zmodp2.add Zmodp2.mul Zmodp2.sub Zmodp2.opp eq.
Proof.
apply mk_rt.
apply Zmodp2_zmod.add_left_id.
apply Zmodp2_zmod.add_comm.
apply Zmodp2_zmod.add_assoc.
apply Zmodp2_ring.mul_left_id.
apply Zmodp2_ring.mul_comm.
apply Zmodp2_ring.mul_assoc.
apply Zmodp2_ring.mul_left_distr.
apply Zmodp2_zmod.add_sub.
move => x. rewrite Zmodp2_zmod.add_comm Zmodp2_zmod.add_left_inv //.
Defined.

Add Ring Zmodp2_ring : Zmodp2_ring.
 *)
Lemma nP_is_nP2 : forall (x1 x2 xs: Zmodp.type),
  forall (p1 : mc curve25519_mcuType), p1#x0 = x1 ->
  forall (p2 : mc curve25519_mcuType), p2#x0 = x2 ->
  (p1 + p2)#x0 = xs ->

  forall (p'1: mc curve25519_Fp2_mcuType), p'1#x0 = Zmodp2.Zmodp2 x1 0 ->
  forall (p'2: mc curve25519_Fp2_mcuType), p'2#x0 = Zmodp2.Zmodp2 x2 0 ->
  (p'1 + p'2)#x0 = Zmodp2.Zmodp2 xs 0.
Proof.
Admitted.
(*   move=> x1 x2 xs [p1 OCp1] Hp1
  [p2 OCp2] Hp2
  [p'1 OCp'1] Hp'1
  [p'2 OCp'2] Hp'2 /= ;
  rewrite /MCGroup.add ?OCp1 ?OCp2 ?OCp'1 ?OCp'2.
  move: p1 OCp1 Hp1 => [|xp1 yp1] OCp1 Hp1.
  +{
    move => <- //.
    move: p'1 OCp'1 Hp'1 => [|xp'1 yp'1] OCp'1 Hp'1.
    - move: Hp2 Hp'2 <- => //=.
    - move: p'2 OCp'2 Hp'2 => [|xp'2 yp'2] OCp'2 Hp'2 //.
      move: Hp1 Hp'1 <- => /= ->.
      move: Hp2 Hp'2 => /= -> <- //=.
      move: Hp1 Hp'1 => /= <- ->.
      case_eq (Zmodp2.Zmodp2 0 0 == xp'2) => eq_xp'2 ; rewrite eq_xp'2 /=.
      * move/eqP:eq_xp'2 => eq_xp'2.
      case_eq ((yp'1 == yp'2) && (yp'1 != 0)) => eq2 ; rewrite eq2 /=.
      rewrite (expr2 (Zmodp2.pi (0,0))).
      rewrite ?GRing.mulr0.
      rewrite ?GRing.add0r.
      rewrite ?GRing.subr0.
      move/andb_prop:eq2 => [].
      move/eqP ->. move/eqP.
      move=> Hyp'2.
      move: Hp2 Hp'2 eq_xp'2 => /= -> ->.
      move: OCp'2 => /=.
      rewrite /b.
      move/eqP.
      rewrite ?GRing.mulr1.
      rewrite ?GRing.mul1r.
      move=>HP2 H2'.
      inversion H2' as [H]; clear H2'.
      move: H HP2. => <-.




      SearchAbout (_ == _ = true).

      move/andb_prop.
      ring.
      rewrite Zmodp2_mulE /=.

      rewrite /GRing.mul /= /Zmodp2.mul /=.
      zmodp_compute.
 ring.
      reflexivity.
      have: (if_spec (Zmodp2.Zmodp2 0 0 == xp'2)).
      move: Hp2 Hp'2 => /= <-.
      

      
  + move: 
  + move => <- /=.
    move: Hp'2 => /=.
    move: Hp2 => /= <- //.
  + move => <- /=.
    move: Hp'1 => /=.
    move: Hp1 => /= <- //.
 
  Search "_ + _".
  rewrite /add.

 *)

Lemma nP_is_nP2' : forall (n:nat) (x xn: Zmodp.type),
  forall (p : mc curve25519_mcuType), p#x0 = x ->
  forall (p': mc curve25519_Fp2_mcuType), p'#x0 = Zmodp2.Zmodp2 x 0 ->
  (p *+ n)#x0 = xn ->
  (p' *+ n)#x0 = Zmodp2.Zmodp2 xn 0.
Proof.
  elim => [|n IHn] x xn p Hp p' Hp'.
  rewrite ?mulr0n /= => <- //.
  rewrite GRing.mulrS.
  rewrite GRing.mulrS.
  elim (p *+ n).
  SearchAbout "*+".