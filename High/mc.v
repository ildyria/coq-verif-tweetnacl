(* --------------------------------------------------------------------
 * (c) Copyright 2011--2012 Microsoft Corporation and Inria.
 * (c) Copyright 2012--2014 Inria.
 * (c) Copyright 2012--2014 IMDEA Software Institute.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype fintype.
From mathcomp Require Import tuple seq fintype bigop ssralg finalg.
From mathcomp Require Import ssrfun choice zmodp fingroup.
From SsrMultinomials Require Import mpoly.
From SsrEllipticCurves Require Import polyall polydec ssrring.
From SsrEllipticCurves Require Export ec.

Import GRing.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

(* -------------------------------------------------------------------- *)
Local Notation simp := Monoid.simpm.

Reserved Notation "\- x" (at level 50).

(* -------------------------------------------------------------------- *)
Record mcuType (K : ringType) := {
  cA : K;
  cB : K;
  pB : cB != 0;
  _  : cA^+2 != 4%:R;
}.

Notation "M '#a'" := (M.(cA)) (at level 30).
Notation "M '#b'" := (M.(cB)) (at level 30).

Section MCUTypeTheory.
  Variable K : ringType.
  Variable M : mcuType K.

  Lemma mcu_b_neq0 : M#b != 0.
  Proof. by case: M. Qed.

  Lemma mcu_asq_neq4 : M#a ^+ 2 != 4%:R.
  Proof. by case: M. Qed.
End MCUTypeTheory.

(* -------------------------------------------------------------------- *)
Section MC.
  Variable K : ringType.
  Variable M : mcuType K.

  Definition oncurve (p : point K) := (
    match p with
    | EC_Inf    => true
    | EC_In x y => M#b * y^+2 == x^+3 + M#a * x^+2 + x
    end).

  Inductive mc : Type := MC p of oncurve p.

  Lemma mc_eq : forall (p q: point K) Hp Hq,
    p = q -> @MC p Hp = @MC q Hq.
  Proof.
    move => p q Hp Hq Heq.
    subst p.
    f_equal.
    apply eq_irrelevance.
  Qed.

  Coercion point_of_mc p := let: MC p _ := p in p.

  Canonical Structure mc_subType := [subType for point_of_mc by mc_rect].

  Definition mc_eqMixin := [eqMixin of mc by <:].
  Canonical Structure mc_eqType := Eval hnf in EqType mc mc_eqMixin.

  Definition mc_choiceMixin := [choiceMixin of mc by <:].
  Canonical Structure mc_choiceType := Eval hnf in ChoiceType mc mc_choiceMixin.

  Lemma oncurve_mc: forall p : mc, oncurve p.
  Proof. exact: valP. Qed.

  Lemma oncurve_0_0: oncurve (|0%:R ,0%:R|).
  Proof. move => /= ; rewrite ?exprS ?expr0 ?mul0r ?mulr0 ?addr0 ; apply/eqP => //.  Qed.

  Lemma oncurve_inf: oncurve ∞.
  Proof. done. Qed.

  Hint Resolve oncurve_mc.
End MC.

Notation "[ 'oc' 'of' p ]" := (oncurve_mc p).

Ltac ssring :=
  let xt := fresh "xt" in
  let xe := fresh "xe" in
    apply/eqP; rewrite -subr_eq0; apply/eqP;
      rewrite ?(mulr0, mul0r, mulr1, mul1r); reify xt xe;
      move: (@Rcorrect _ 100 xe [::] xt (Ring_polynom.PEc 0) I (erefl true));
      by rewrite !PEReval.

(* -------------------------------------------------------------------- *)
Section XPoly.
  Variable K : ringType.
  Variable M : mcuType K.

  Local Notation a := (M#a).
  Local Notation b := (M#b).

  Definition Xpoly := locked (Poly [:: 0; 1; a; 1]).

  Lemma size_Xpoly : size Xpoly = 4.
  Proof.
    by unlock Xpoly; rewrite (@PolyK _ 0) //= oner_neq0.
  Qed.

  Lemma XpolyE: Xpoly = 'X^3 + a *: 'X^2 + 'X.
  Proof.
    apply/polyP => i; unlock Xpoly; rewrite (@PolyK _ 0) ?oner_neq0 //.
    rewrite !coef_add_poly coefZ !coefXn coefX; move: i.
    by do 5! (case; first by rewrite !simp); move=> ?; rewrite /= !simp.
  Qed.

  Lemma XpolyN0: Xpoly != 0.
  Proof. by rewrite -size_poly_eq0 size_Xpoly. Qed.

  Lemma horner_Xpoly:
    forall x, Xpoly.[x] = x ^+ 3 + a * x ^+ 2 + x.
  Proof. by move=> x; rewrite XpolyE !(hornerXn, hornerE). Qed.

  Lemma Xpoly_oncurve c:
    (root Xpoly c) = oncurve M (|c, 0|).
  Proof.
    by rewrite rootE horner_Xpoly /= [0^+2]expr2 !mulr0 eq_sym.
  Qed.

  Lemma oncurve_root x y: oncurve M (|x, y|) = root (b *: 'X ^+ 2 - (Xpoly.[x])%:P) y.
  Proof.
    by rewrite rootE !(hornerE, hornerXn, horner_Xpoly) subr_eq0 /= !expr2 !mulrA.
  Qed.

  Lemma Xpoly_monic: Xpoly \is monic.
  Proof.
    apply/monicP; unlock lead_coef Xpoly.
    by rewrite !(PolyK (c := 0)) //= oner_eq0.
  Qed.

(*  Lemma map_XpolyE (rT : ringType) (f : {rmorphism K -> rT}):
    map_poly f Xpoly = 'X^3 + (f a) *: 'X + (f b)%:P.
  Proof.
    pose rwE := (rmorphD, map_polyC, map_polyZ, map_polyXn, map_polyX).
    by rewrite XpolyE; do! rewrite !rwE /=.
  Qed.*)
End XPoly.

(* -------------------------------------------------------------------- *)
Module MCGroup.
  Section Defs.
    Variable K : ecuFieldType.
    Variable M : mcuType K.

    Local Notation Xpoly := (@Xpoly _ M).

    Lemma eqrN_eq0 (y : K): (y == -y) = (y == 0).
    Proof.
      rewrite -addr_eq0 -{1 2}[y]mul1r -mulrDl.
      by rewrite mulf_eq0 (negbTE (ecu_chi2 K)).
    Qed.

    Definition neg (p : point K) :=
      if p is (|x, y|) then (|x, -y|) else ∞.

    Definition add_check (p1 p2 : point K) :=
      let p1 := if oncurve M p1 then p1 else ∞ in
      let p2 := if oncurve M p2 then p2 else ∞ in

        match p1, p2 with
        | ∞, _ => p2 | _, ∞ => p1

        | (|x1, y1|), (|x2, y2|) =>
          if   x1 == x2
          then if   (y1 == y2) && (y1 != 0)
               then
                 let s  := (3%:R * x1^+2 + 2%:R * M#a * x1 + 1) / (2%:R * M#b * y1) in
                 let xs := s^+2 * M#b - M#a - 2%:R * x1 in
                   (| xs, - s * (xs - x1) - y1 |)
               else
                 ∞
          else
            let s  := (y2 - y1) / (x2 - x1) in
            let xs := s^+2 * M#b - M#a - x1 - x2 in
              (| xs, - s * (xs - x1) - y1 |)
        end.

    Definition add (p1 p2 : point K) :=
        match p1, p2 with
        | ∞, _ => p2 | _, ∞ => p1

        | (|x1, y1|), (|x2, y2|) =>
          if   x1 == x2
          then if   (y1 == y2) && (y1 != 0)
               then
                 let s  := (3%:R * x1^+2 + 2%:R * M#a * x1 + 1) / (2%:R * M#b * y1) in
                 let xs := s^+2 * M#b - M#a - 2%:R * x1 in
                   (| xs, - s * (xs - x1) - y1 |)
               else
                 ∞
          else
            let s  := (y2 - y1) / (x2 - x1) in
            let xs := s^+2 * M#b - M#a - x1 - x2 in
              (| xs, - s * (xs - x1) - y1 |)
        end.

    Lemma add_no_check_eq (p1 p2:point K) :
      oncurve M p1 ->
      oncurve M p2 ->
      add p1 p2 = add_check p1 p2.
    Proof.
      rewrite /add /add_check => -> -> //.
    Qed.

    Lemma zeroO : oncurve M ∞.
    Proof. by []. Defined.

    Lemma negO : forall p, oncurve M p -> oncurve M (neg p).
    Proof. by case=> [|x y] //=; rewrite sqrrN. Defined.

    Lemma oncurveN p: (oncurve M p) = (oncurve M (neg p)).
    Proof.
      apply/idP/idP; move/negO => //.
      by case: p => [|x y] //=; rewrite opprK.
    Defined.

    Lemma oncurveN_fin x y: oncurve M (|x, -y|) = oncurve M (|x, y|).
    Proof. by move: (oncurveN (|x, y|)). Defined.

    Local Notation sizep := (size : {poly _} -> _).

    (* if (u, v, c) = line p q, then the line u*y + v*x = c runs through p and q *)
    Definition line (p q : K * K) : K * K * K :=
      let: (x1, y1) := p in
      let: (x2, y2) := q in

      match oncurve M (|x1, y1|) && oncurve M (|x2, y2|) with
      | false => (0, 0, 0)
      | true  =>
          if   x1 == x2
          then if   (y1 == y2) && (y1 != 0)
               then
                 let s := (3%:R * x1^+2 + 2%:R * M#a * x1 + 1) / (2%:R * M#b * y1) in
                   (1, -s, y2 - s * x2)
               else
                 (0, 1, x1)
          else
            let s := (y2 - y1) / (x2 - x1) in
              (1, -s, y2 - s * x2)
      end.

    (* add two points geometrically *)
    Definition ladd (p1 p2 : point K) :=
      let p1 := if oncurve M p1 then p1 else ∞ in
      let p2 := if oncurve M p2 then p2 else ∞ in

        match p1, p2 with
        | ∞, _ => neg p2 | _, ∞ => neg p1
        | (|x1, y1|), (|x2, y2|) =>
            let: (u, v, c) := line (x1, y1) (x2, y2) in
              if u == 0 then ∞ else
                let: x := u^-2 * v ^+ 2 * M#b - M#a - (x1 + x2) in
                let: y := u^-1 * (c - v * x) in
                  (|x, y|)
        end.

    Lemma ladd_addE p q: ladd p q = neg (add_check p q).
    Proof.
      rewrite /ladd /add_check;
        set pp := if oncurve M p then _ else _;
        set qq := if oncurve M q then _ else _.
      have oncve_pp: oncurve M pp by rewrite {}/pp; case h: (oncurve M p).
      have oncve_qq: oncurve M qq by rewrite {}/qq; case h: (oncurve M q).
      move: {p q} pp oncve_pp qq oncve_qq.
      case=> [|x1 y1] oncve_1 [|x2 y2] oncve_2 //.
      rewrite /line oncve_1 oncve_2 /=.
      case: (x1 =P x2); first (case: andP; first last).
      + by move=> _ _; rewrite eqxx.
      + case=> /eqP <- nz_y1 <-; rewrite oner_eq0.
        rewrite !(simp, expr1n, invr1, opprD, opprK) /=.
        by set s := ((_ + 1) / _); congr (|_, _|); ssring.
      + move/eqP => ne_x1x2; rewrite oner_eq0.
        rewrite !(simp, expr1n, invr1, opprD, opprK) /=.
        set s := (y2 - y1) / _; congr (|_, _|); first by ssring.
        set l := (y2 - _ - _); set r := - _.
          have {l}->: l = s^+3 * M#b - s * (M#a + x1 + x2) + (y2 - s * x2) by ssring.
          have {r}->: r = s^+3 * M#b - s * (M#a + x1 + x2) + (y1 - s * x1) by ssring.
        have nz_x2Bx1: x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
        congr (_ + _); apply/(@mulfI _ (x2 - x1)) => //.
        by rewrite !mulrBr !mulrA [_ / _]mulrAC divff // !simp; ssring.
    Defined.

    Lemma line_outcveE p q:
         ~~ (oncurve M (|p.1, p.2|) && oncurve M (|q.1, q.2|))
      -> line p q = (0, 0, 0).
    Proof. by case: p q => [x1 y1] [x2 y2]; rewrite /line => /negbTE ->. Qed.

    Lemma line_sym p q: line p q = line q p.
    Proof.
      case: p q => [x1 y1] [x2 y2]; rewrite /line;
        have [oncve_1 | outcve_1] := (boolP (oncurve M (|x1, y1|)));
        have [oncve_2 | outcve_2] := (boolP (oncurve M (|x2, y2|))) => //=.
      rewrite ![x2==_]eq_sym; case: (x1 =P x2) => [<-|/eqP ne_x1x2]; last first.
        rewrite -![y2 - y1]opprB -![x2 - x1]opprB !invrN !mulrNN.
        congr (_, _, _); rewrite [X in _-X=_]mulrAC [X in _=_-X]mulrAC.
        rewrite -[X in X+_=_]divr1 -[X in _=X+_]divr1 -!mulNr.
        rewrite !addf_div ?(oner_neq0, subr_eq0, ne_x1x2) // !simp.
        by congr (_ / _); rewrite !opprB !(mulrDl, mulrDr); ssring.
      rewrite ![y2==_]eq_sym; case: (y1 =P y2) => [<-|/eqP ne_y1y2] => //=.
      by rewrite [0==y1]eq_sym; have [->|->] := (eqVneq y1 0); rewrite ?eqxx.
    Qed.

    Lemma line_okl p q:
      let: (u, v, c) := line p q in
        u * p.2 + v * p.1 - c = 0.
    Proof.
      case: p q => [x1 y1] [x2 y2]; rewrite /line;
        have [oncve_1 | outcve_1] := (boolP (oncurve M (|x1, y1|)));
        have [oncve_2 | outcve_2] := (boolP (oncurve M (|x2, y2|)));
          rewrite ?(simp, oppr0) //=.
      case: (x1 =P x2) => [<-|/eqP ne_x1x2]; last first.
        rewrite !simp /= mulNr ![_ / _ * _]mulrAC opprD opprK !addrA.
        rewrite [_-y2]addrAC -!addrA -mulNr -mulrDl !addrA.
        rewrite -[y1-y2]divr1 addf_div ?(oner_eq0, subr_eq0) 1?eq_sym //.
        apply/eqP; rewrite !simp /=.
        rewrite mulf_eq0 invr_eq0 orbC subr_eq0 eq_sym (negbTE ne_x1x2) /=.
        by apply/eqP; ssring.
      case: (y1 =P y2) => [<-|/eqP ne_y1y2] /=; last by rewrite !simp subrr.
      have [->|nz_y1] := eqVneq y1 0; first by rewrite eqxx /= !simp subrr.
      by rewrite nz_y1 !simp; ssring.
    Qed.

    Lemma line_okr p q:
      let: (u, v, c) := line p q in
        u * q.2 + v * q.1 - c = 0.
    Proof. by rewrite line_sym; apply: line_okl. Qed.

    Lemma thdimp p q:
      let: (u, v, c) := line p q in
      let: r := Xpoly - M#b *: (u^-1 *: (v *: 'X - c%:P)) ^+ 2 in
      let: z := u ^- 2 * v ^+ 2 * M#b - M#a - (p.1 + q.1) in
        u != 0 -> r = ('X - p.1%:P) * ('X - q.1%:P) * ('X - z%:P).
    Proof.
      set pp := (|p.1, p.2|); set qq := (|q.1, q.2|).
      case: (boolP (oncurve M pp && oncurve M qq)); last first.
        by move/line_outcveE=> ->; rewrite eqxx.
      case/andP=> oncve_p oncve_q; case lE: (line p q) => [[u v] c].
      move=> nz_u; set r := (Xpoly - _);
        set c0 := -M#b * u^-2 * c^+2;
        set c1 := 1 + (u^-2 * M#b * v * c) *+ 2;
        set c2 := M#a - u^-2 * v^+2 * M#b;
          have Er: r = Poly [:: c0; c1; c2; 1].
      + apply/polyP=> i; unlock Xpoly; rewrite (@PolyK _ 0) //= ?oner_neq0 //.
        pose coefE := (coefMC, coefCM, coefE).
        rewrite /r XpolyE !(exprZn, sqrrB) !coefE; move: i.
        do 4! (case; first by rewrite exprVn !(simp, oppr0, eqxx) //=; ssring).
        by move=> i; rewrite !simp /= !(oppr0, mulr0) nth_nil.
      have sz_r: size r = 4 by rewrite Er (@PolyK _ 0) // oner_eq0.
      have nz_r: r != 0 by rewrite -size_poly_eq0 sz_r.
      have monic_r: r \is monic.
        apply/monicP; rewrite Er lead_coefE -{2}Er sz_r.
        by rewrite (@PolyK _ 0) // oner_neq0.
      have root_pVq: forall s, (s == p) || (s == q) -> root r s.1.
        move=> s eq_s_pq; have oncve_s: oncurve M (|s.1, s.2|).
          by case/orP: eq_s_pq => /eqP ->.
        have: u * s.2 + v * s.1 - c = 0.
          case/orP: eq_s_pq => /eqP->.
          + by move: (line_okl p q); rewrite lE.
          + by move: (line_okr p q); rewrite lE.
        move/eqP; rewrite -addrA addrC addr_eq0 => /eqP vsBcE.
        rewrite rootE /r !(horner_exp, hornerE) /= vsBcE.
        rewrite -![_ / u * _]mulrA -mulrA -expr2 mulrN sqrrN [u^-1 * _]mulrA mulVf // mul1r.
        by rewrite horner_Xpoly -(eqP oncve_s) subrr.
      have h: forall x, count (pred1 x) [:: p.1; q.1] <= \mu_x r.
        move=> x /=; rewrite addn0; case: (p.1 =P x); last first.
          move/eqP=> ne_p1x; rewrite add0n; case: (q.1 =P x) => //=.
          move=> <-; rewrite mu_gt0 //; apply: root_pVq.
          by rewrite eqxx orbT.
        move=> /esym Exp; case: (q.1 =P x); last first.
          move/eqP=> ne_q1x; rewrite addn0 /= mu_gt0 // Exp.
          by apply: root_pVq; rewrite eqxx.
        move=> /esym Exq /=; rewrite addn1; move: lE.
        have pairE: forall x, (x.1, x.2) = x by move=> ?? [].
        rewrite /line -[p]pairE -[q]pairE {pairE} oncve_p oncve_q /=.
        rewrite -Exp -Exq eqxx /=; case: andP; last first.
          by move=> _ [/esym z_u _ _]; rewrite z_u eqxx in nz_u.
        case=> [/eqP eq_p2q2 nz_q2] [/esym one_u /esym Ev /esym Ec].
        apply: ltn_pred; rewrite /= -subn1 -mu_deriv_char; first last.
        + by rewrite Exp; apply: root_pVq; rewrite eqxx.
        + rewrite sz_r; case => [|[|[|[|i]]]] // _.
          * by rewrite inE /= ecu_chi2.
          * by rewrite inE /= ecu_chi3.
        rewrite mu_gt0; last first.
          rewrite Er /deriv -{1}Er sz_r -size_poly_eq0.
          by rewrite polyseq_poly // (@PolyK _ 0) //= ?(oner_neq0, ecu_chi3).
        rewrite rootE /deriv /horner sz_r polyseq_poly; last first.
          by rewrite Er (@PolyK _ 0) ?(oner_neq0, ecu_chi3).
        rewrite Er (@PolyK _ 0) ?oner_eq0 //= mul0r add0r mulr1n.
        rewrite /c2 /c1 one_u expr1n invr1 !(mul1r, mulN1r).
        set w := (_ + _ : K); pose k := 3%:R * x^+2 + 2%:R * M#a * x + 1.
        have {w} ->: w = k - 2%:R * M#b * x * v^+2 + 2%:R * M#b * (c * v) by ssring.
        pose w := (2%:R * M#b * p.2); apply/eqP/(@mulIf _ (w^+2)).
          by rewrite expf_neq0 // !mulf_neq0 // ?ecu_chi2 // mcu_b_neq0.
        rewrite mul0r 2!mulrDl !mulNr.
        have ->:  2%:R * M#b * (c * v) * w ^+ 2 = 2%:R * M#b * (c * w) * (v * w) by ssring.
        have ->: (2%:R * M#b * x * v ^+ 2) * w ^+ 2 = 2%:R * M#b * x * (v * w)^+2 by ssring.
        have ->: v * w = - (3%:R * x ^+ 2 + 2%:R * M #a * x + 1).
          rewrite Ev /w -mulNr -mulrA mulVf ?mulr1 //.
          by rewrite !mulf_neq0 // ?ecu_chi2 // mcu_b_neq0.
        have ->: c * w = q.2 * w - (3%:R * x ^+ 2 + 2%:R * M #a * x + 1) * x.
          rewrite Ec /w mulrBl; congr (_ - _); rewrite mulrAC.
          congr (_ * _); rewrite -[_ / _ * _]mulrA mulVf ?mulr1 //.
          by rewrite !mulf_neq0 // ?ecu_chi2 // mcu_b_neq0.
        by rewrite -eq_p2q2 {}/w {}/k Exp; ssring.
      have: ('X - p.1%:P) * ('X - q.1%:P) %| r.
        move: (@roots_dvdp _ r [:: p.1; q.1]).
        rewrite !big_cons big_nil mulr1; apply.
        by apply/allP=> x _; rewrite inE; apply: h.
      case/dvdpP=> qr Er'; have/(congr1 sizep) := Er'.
      have := nz_r; rewrite {1}Er' mulf_eq0 => /norP [nz_qr _].
      rewrite sz_r !size_mul // ?(mulf_neq0, polyXsubC_eq0) //.
      rewrite !size_XsubC /= addn3 /=; case=> /esym/eqP.
      case/size_polyf2P=> k; rewrite eqp_monic ?monicXsubC //; last first.
        by move: monic_r; rewrite Er' !(monicMr, monicXsubC) //.
      move/eqP=> Eqr {nz_qr}; move: Er'; rewrite {}Eqr => Er'.
      have/(congr1 (fun (x : {poly K})=> x`_2)) := Er'.
      set cs := [tuple k; p.1; q.1]; move/esym/eqP: (mroots_sum cs).
      rewrite 3!big_cons big_nil mulr1 eqr_oppLR => /eqP->.
      rewrite {1}Er (@PolyK _ 0) ?oner_neq0 // unlock /= !simp /=.
      move=> Ec2; have: k = - (c2 + p.1 + q.1) by rewrite Ec2; ssring.
      move=> Ek; move: Er'; rewrite Ek=> ->.
      rewrite !mulrA [X in _ = X]mulrC !mulrA; congr (_ * _ * _).
      by rewrite -!polyC_opp opprK /c2; congr ('X + _%:P); ssring.
    Qed.

    Lemma negK: involutive neg.
    Proof. by case=> [|x y] //=; rewrite opprK. Qed.

    Lemma addO_check p q: oncurve M (add_check p q).
    Proof.
      rewrite oncurveN -ladd_addE /ladd;
        set pp := if oncurve M p then _ else _;
        set qq := if oncurve M q then _ else _.
      have oncve_pp: oncurve M pp by rewrite {}/pp; case h: (oncurve M p).
      have oncve_qq: oncurve M qq by rewrite {}/qq; case h: (oncurve M q).
      move: {p q} pp oncve_pp qq oncve_qq.
      case=> [|x1 y1] oncve_1 [|x2 y2] oncve_2; rewrite -?oncurveN //.
      case h: (line _ _) => [[u v] c]; case: (u =P 0) => //.
      move/eqP=> nz_u; set z := u ^- 2 * v ^+ 2 * M#b - M#a - (x1 + x2).
      move: (thdimp (x1, y1) (x2, y2)); rewrite h => /(_ nz_u) /=.
      move/(congr1 (fun p => p.[z]))/esym; rewrite -/z.
      rewrite hornerM hornerXsubC subrr mulr0 => /esym/eqP.
      rewrite 2!hornerE subr_eq0 horner_Xpoly => /eqP->.
      apply/eqP; rewrite -mul_polyC !(horner_exp, hornerE) /=.
      rewrite -![(_ / u) * _]mulrA -![M#b * _ * _]mulrA -!expr2.
      by rewrite !exprMn; congr (_ * _); rewrite -[c-_]opprK opprB sqrrN.
    Defined.

    Lemma addO' p q: oncurve M p -> oncurve M q -> oncurve M (add p q).
    Proof.
    move => Hp Hq.
    rewrite (add_no_check_eq Hp Hq).
    apply addO_check.
    Qed.

    Lemma addO (p q: mc M): oncurve M (add p q).
    Proof.
    destruct p as [p Hp], q as [q Hq].
    by apply addO'.
    Qed.

    Lemma add0o : {in (oncurve M), left_id ∞ add}.
    Proof. done. Qed.

    Lemma addNo_check : {in (oncurve M), left_inverse ∞ neg add_check}.
    Proof.
      move=> p; rewrite /add_check -oncurveN.
      have [|] := (boolP (oncurve M p)) => // _.
      case: p=> [|x y] //=; rewrite eqxx /= eq_sym; case Hy0: (y == 0).
      + by rewrite (eqP Hy0) oppr0 eqxx //.
      + rewrite oppr_eq0 Hy0 andbT; case HyN: (y == -y) => //=.
        by absurd false=> //; rewrite -Hy0 -eqrN_eq0 HyN.
    Qed.

    Lemma addNo : {in (oncurve M), left_inverse ∞ neg add}.
    Proof.
      move=> p.
      rewrite /in_mem /mem => /= Hp.
      rewrite add_no_check_eq //.
      2: rewrite -oncurveN //.
      by apply addNo_check.
    Qed.

    Lemma addoC_check : commutative add_check.
    Proof.
      move=> p1 p2; rewrite /add_check;
        have [|] := (boolP (oncurve M p1)) => // _;
        have [|] := (boolP (oncurve M p2)) => // _; first last.
      + by case: p2.
      + by case: p1.
      case: p1 p2 => [|x1 y1] [|x2 y2] //=.
      rewrite [x2 == _]eq_sym [y2 == _]eq_sym.
      case Ex: (x1 == x2); first (case Ey: (y1 == y2)) => //=.
      + by rewrite -(eqP Ey) -(eqP Ex); case Ey0: (y1 == 0).
      + congr (| _, _ |); first (rewrite -!addrA; congr (_^+2 * M#b + (-M#a + _))).
        * by rewrite -[y2 - _]opprB -[x2 - _]opprB invrN mulrNN.
        * by rewrite addrC.
      rewrite -[y2 - _]opprB -[x2 - _]opprB invrN mulrNN.
      set Dx := (x1 - x2); set Dy := (y1 - y2); set a := Dy / Dx.
      have HDx: Dx != 0 by apply/negP; rewrite subr_eq0 Ex.
      rewrite !mulrDr -!addrA; congr (-a * (a^+2 * M#b) + (-a * -M#a + _)); rewrite !mulrNN.
      rewrite ![a * x1 + _]addrCA; congr (_ + (_ + _)).
      rewrite ![a * _]mulrC /a !mulrA -[y1]mul1r -[y2]mul1r.
      rewrite -[1](divff HDx) ![Dx / Dx * _]mulrAC.
      rewrite -!mulrBl; congr (_ / _).
      rewrite /Dx /Dy !mulrDl !mulrDr !mulNr !mulrN.
      rewrite !opprB !addrA [_ - (_ * y1)]addrC !addrA addNr add0r.
      symmetry; rewrite -[_ - _ + _]addrA addNr addr0.
      by rewrite addrC.
    Qed.

    Lemma addoC : prop_in2 (mem (oncurve M)) (P:=fun x y : point K =>  eq (add x y) (add y x))
 (inPhantom (commutative add)).
    Proof.
      move=> p q.
      rewrite /in_mem /mem => /= Hp Hq.
      rewrite ?add_no_check_eq //.
      apply addoC_check.
    Qed.

    Notation   zeromc := (MC zeroO).
    Definition negmc  := [fun p     : mc M => MC (negO [oc of p])].
    Definition addmc  := [fun p1 p2 : mc M => MC (addO p1 p2)].

    Lemma addNm : left_inverse zeromc negmc addmc.
    Proof. by move=> [p Hp]; apply/eqP; rewrite eqE /= addNo. Qed.

    Lemma add0m : left_id zeromc addmc.
    Proof. by move=> [p Hp]; apply/eqP; rewrite eqE /=. Qed.

    Lemma addmC : commutative addmc.
    Proof.
      move=> [p1 Hp1] [p2 Hp2]; apply/eqP=> /=.
      by rewrite eqE /= addoC.
    Qed.

  End Defs.
End MCGroup.
