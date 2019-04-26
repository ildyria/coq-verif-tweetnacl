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
From Tweetnacl.High Require Import Zmodp2_rules.
From Tweetnacl.High Require Import curve25519_Fp2.
From Tweetnacl.High Require Import curve25519_twist25519_eq.
From Tweetnacl.High Require Import Zmodp.
Require Import Ring.
Require Import ZArith.

(* Import BinInt. *)

Open Scope ring_scope.
Import GRing.Theory.

Local Notation "p '#x0'" := (point_x0 p) (at level 30).
Local Notation "Z.R A" := (Zmodp.repr A) (at level 30).
Local Notation "-. A" := (Zmodp.opp A) (at level 30).

Lemma oncurve_inf : oncurve curve25519_Fp2_mcuType (EC_Inf Zmodp2.type).
Proof. done. Defined.

Local Lemma oncurve_00 : (oncurve curve25519_Fp2_mcuType (EC_In 0 0)).
Proof.
  simpl; rewrite /a /b ; apply/eqP.
  have ->: (0 ^+ 2)%R = 0 :> Zmodp2.type by ring_simplify_this.
  have ->: (0 ^+ 3)%R = 0 :> Zmodp2.type by ring_simplify_this.
  rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
  f_equal; f_equal; apply/eqP ; zmodp_compute => //=.
Qed.

Lemma oncurve25519_impl : forall (x y: Zmodp.type),
oncurve curve25519_mcuType (EC_In x y) ->
(oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (x, Zmodp.pi 0)) (Zmodp2.pi (y, Zmodp.pi 0)))).
Proof.
move => x y /=.
rewrite /a /b.
rewrite ?expr2 ?expr3 ?expr3'.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
rewrite /curve25519.a /curve25519.b.
ring_simplify_this.
move/eqP => -> /=.
apply/eqP.
f_equal.
Qed.

Local Lemma oncurve25519 : forall x k k0 : Zmodp.type,
curve25519.b * k0 ^+ 2 == k ^+ 3 + curve25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have : oncurve curve25519_mcuType (EC_In k k') => //.
move/oncurve25519_impl => HOC.
exists (MC HOC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

Lemma ontwist25519_impl : forall (x y: Zmodp.type),
oncurve twist25519_mcuType (EC_In x y) ->
(oncurve curve25519_Fp2_mcuType (EC_In (Zmodp2.pi (x, Zmodp.pi 0)) (Zmodp2.pi (Zmodp.pi 0, y)))).
Proof.
move => x y /=.
rewrite /a /b.
rewrite ?expr2 ?expr3 ?expr3'.
rewrite ?Zmodp2_mulE /= ?Zmodp2_addE /=.
rewrite /twist25519.a /twist25519.b.
ring_simplify_this.
move/eqP => -> /=.
apply/eqP.
f_equal.
Qed.

Local Lemma ontwist25519 : forall x k k0 : Zmodp.type,
twist25519.b * k0 ^+ 2 == k ^+ 3 + twist25519.a * k ^+ 2 + k ->
k = x -> exists p0 : mc curve25519_Fp2_mcuType, p0 #x0 = Zmodp2.Zmodp2 x 0.
Proof.
move => x k k' Hx <-. clear x.
have : oncurve twist25519_mcuType (EC_In k k') => //.
move/ontwist25519_impl => HOC.
exists (MC HOC) => /=.
have ->: Zmodp.pi 0 = Zmodp.zero => //=.
Qed.

(* May actually not be in the right direction... *)
Theorem x_is_on_curve_or_twist_implies_x_in_Fp2: forall (x:Zmodp.type),
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

Definition curve_Fp_to_Fp2 (p: point Zmodp.type) : (point Zmodp2.type) :=
match p with
  | EC_Inf => EC_Inf Zmodp2.type
  | EC_In x y => EC_In (Zmodp2.Zmodp2 x 0) (Zmodp2.Zmodp2 y 0)
end.

Definition twist_Fp_to_Fp2 (p: point Zmodp.type) : (point Zmodp2.type) :=
match p with
  | EC_Inf => EC_Inf Zmodp2.type
  | EC_In x y => EC_In (Zmodp2.Zmodp2 x 0) (Zmodp2.Zmodp2 0 y)
end.

Lemma curve_add_Fp_to_Fp2 : forall (p q: point Zmodp_ringType) (p' q': point Zmodp2_ringType),
  p' = curve_Fp_to_Fp2 p ->
  q' = curve_Fp_to_Fp2 q ->
  MCGroup.add_no_check curve25519_Fp2_mcuType p' q' = curve_Fp_to_Fp2 (MCGroup.add_no_check curve25519_mcuType p q).
Proof.
  move => [|xp yp] [|xq yq] [|xp' yp'] [|xq' yq'] //= [] -> -> [] -> ->.
  rewrite /curve25519.a /curve25519.b.
  match goal with
    | [ |- _ = ?A ] => remember A as Freezer
  end.
  rewrite /eq_op /Equality.op /=.
  rewrite /eq_op /Equality.op /=.
  rewrite !eq_refl ?Bool.andb_true_r.
  rewrite ?expr2.
  have ->: 2%:R = Zmodp2.Zmodp2 (2%:R) 0 => //.
  have ->: 3%:R = Zmodp2.Zmodp2 (3%:R) 0 => //.
  Zmodpify => /=.
  ringify.
  subst Freezer.
  ring_simplify_this.
  case_eq (xp == xq) => -> //=.
  case_eq ((yp == yq) && (yp != 0)) => -> //=.
Qed.

Lemma twist_add_Fp_to_Fp2 : forall (p q: point Zmodp_ringType) (p' q': point Zmodp2_ringType),
  p' = twist_Fp_to_Fp2 p ->
  q' = twist_Fp_to_Fp2 q ->
  MCGroup.add_no_check curve25519_Fp2_mcuType p' q' = twist_Fp_to_Fp2 (MCGroup.add_no_check twist25519_mcuType p q).
Proof.
  move => [|xp yp] [|xq yq] [|xp' yp'] [|xq' yq'] //= [] -> -> [] -> ->.
  rewrite /twist25519.a /twist25519.b.
  match goal with
    | [ |- _ = ?A ] => remember A as Freezer
  end.
  rewrite /eq_op /Equality.op /=.
  rewrite /eq_op /Equality.op /=.
  rewrite !eq_refl ?Bool.andb_true_r.
  rewrite ?expr2.
  have ->: 2%:R = Zmodp2.Zmodp2 (2%:R) 0 => //.
  have ->: 3%:R = Zmodp2.Zmodp2 (3%:R) 0 => //.
  Zmodpify => /=.
  subst Freezer.
  ringify.
  ring_simplify_this.
  case_eq (xp == xq) => -> ; rewrite -Zmodp_mul_comm_2 ?GRing.mulrA //=.
  case_eq ((yp == yq) && (yp != 0)) => -> //=.
Qed.




(* a great definition ... *)
(* Definition curve_to_Fp2 (p: mc curve25519_mcuType) : (mc curve25519_Fp2_mcuType) :=
match p with
  | MC u P =>
  match u, P with 
  | EC_Inf, _ => MC (MCGroup.zeroO curve25519_Fp2_mcuType)
  | EC_In x y, P => MC (oncurve25519_impl x y P)
  end
end.
 *)
(* a not so great definition ... *)

(* 
Lemma curve_to_Fp2_inf : curve_to_Fp2 (MC (MCGroup.zeroO curve25519_mcuType)) = MC (MCGroup.zeroO curve25519_Fp2_mcuType).
Proof. done. Qed.
*)
(* Lemma curve_to_Fp2_xy x y (P: oncurve curve25519_mcuType (|x , y|)): curve_to_Fp2 (MC P) = MC (oncurve25519_impl x y P).
Proof. done. Qed.
 *)
(* a not so great definition ... *)
(* Definition curve_to_Fp2 (p: point Zmodp.type) : (point Zmodp2.type) :=
match p with
  | EC_Inf => EC_Inf Zmodp2.type
  | EC_In x y => EC_In (Zmodp2.Zmodp2 x 0) (Zmodp2.Zmodp2 y 0)
end.
 *)
(* a great definition ... *)
(* Definition twist_to_Fp2 (p: mc twist25519_mcuType) : (mc curve25519_Fp2_mcuType) :=
match p with
  | MC (EC_Inf) _ => MC oncurve_inf
  | MC (EC_In x y) P => MC (ontwist25519_impl x y P)
end.
 *)
(* a not so great definition ... *)
(* Definition twist_to_Fp2 (p: point Zmodp.type) : (point Zmodp2.type) :=
match p with
  | EC_Inf => EC_Inf Zmodp2.type
  | EC_In x y => EC_In (Zmodp2.Zmodp2 x 0) (Zmodp2.Zmodp2 0 y)
end.
 *)




(* Lemma nP_is_nP2 : forall (x1 x2 xs: Zmodp.type),
  forall (p1 : mc curve25519_mcuType), p1#x0 = x1 ->
  forall (p2 : mc curve25519_mcuType), p2#x0 = x2 ->
  (p1 + p2)#x0 = xs ->

  forall (p'1: mc curve25519_Fp2_mcuType), p'1#x0 = Zmodp2.Zmodp2 x1 0 ->
  forall (p'2: mc curve25519_Fp2_mcuType), p'2#x0 = Zmodp2.Zmodp2 x2 0 ->
  (p'1 + p'2)#x0 = Zmodp2.Zmodp2 xs 0.
Proof.
Admitted.
 *)
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

(* Lemma nP_is_nP2' : forall (n:nat) (x xn: Zmodp.type),
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
  SearchAbout "*+". *)