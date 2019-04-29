Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple seq fintype bigop ssralg finalg.
From mathcomp Require Import choice zmodp fingroup.
From SsrMultinomials Require Import mpoly.
From SsrEllipticCurves Require Import polyall polydec ssrring.
From SsrEllipticCurves Require Export ec.
From Tweetnacl.High Require Import mc.

Import GRing.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Section MontgomerysFormulas.
  Variable K : ecuFieldType.
  Variable M : mcuType K.

  Local Notation "\- x"   := (@MCGroup.neg _ x).
  Local Notation "x \+ y" := (@MCGroup.add _ M x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Lemma same_x_opposite_points p1_x p1_y p2_x p2_y :
    let p1 := (|p1_x, p1_y|) in
    let p2 := (|p2_x, p2_y|) in
    oncurve M p1 -> oncurve M p2 ->
    p1_x = p2_x -> p1 != p2 -> p1 = \- p2.
  Proof.
    move=> p1 p2 oncve_p1 oncve_p2 x1_eq_x2 p1_neq_p2.
    congr (|_, _|); first by [].
    apply/eqP; rewrite -[_==_]orFb.
    have /negbTE <-: p1_y != p2_y.
      apply: (@contra _ (p1 == p2)); last by assumption.
      by move/eqP=> y1_eq_y2; apply/eqP; congr (|_, _|).
    rewrite -eqf_sqr.
    apply/eqP/(@mulfI _ (M#b)); first exact: mcu_b_neq0.
    move: oncve_p2 oncve_p1 => /eqP-> /eqP->.
    by rewrite x1_eq_x2.
  Qed.

  Definition point_x0 (p : point K) :=
    if p is (|x, _|) then x else 0.

  Local Notation "p '#x'" := (point_x0 p) (at level 30).

  Definition point_is_fin (p : point K) :=
    if p is ∞ then false else true.

  Lemma pointE: forall p : point K,
    point_is_fin p -> exists x y, p = (|x, y|).
  Proof. by elim => // x y _; exists x; exists y. Qed.

  Variable p1 p2 : point K.
  Let p3 := p1 \+ p2.
  Let p4 := p1 \- p2.

  Lemma add_finite_different_x : oncurve M p1 -> oncurve M p2 ->
    all point_is_fin [:: p1; p2; p3] -> p1 != p2 -> p1#x != p2#x.
  Proof.
    move=> oncve_p1 oncve_p2.
    move/andP; elim=> Hfin_p1; move/andP; elim=> Hfin_p2; move/andP;
      elim=> Hfin_p3 _ p1_neq_p2.
    have [x1 [y1 Hp1]] : exists x1 y1, p1 = (|x1, y1|)
      by apply: pointE.
    have [x2 [y2 Hp2]] : exists x2 y2, p2 = (|x2, y2|)
      by apply: pointE.
    apply: contraT => /negbNE/eqP x1_eq_x2.
    have p1_eq_p2N: p1 = \- p2.
      rewrite Hp1 Hp2 in p1_neq_p2 x1_eq_x2 oncve_p1 oncve_p2 *.
      by apply: same_x_opposite_points.
    have p1_plus_p2_inf: p3 = ∞
      by rewrite /p3 p1_eq_p2N MCGroup.addNo //.
    have p3_not_fin: ~~point_is_fin p3
      by rewrite p1_plus_p2_inf //.
    by rewrite -(andbN (point_is_fin p3)) p3_not_fin Hfin_p3.
  Qed.

  Lemma montgomery_neq : oncurve M p1 -> oncurve M p2 -> p1 != p2 ->
    all point_is_fin [:: p1; p2; p3] ->
    p3#x * p4#x * (p1#x - p2#x)^+2 = (p1#x * p2#x - 1)^+2.
  Proof.
    move=> oncve_p1 oncve_p2 p1_neq_p2 Hall_fin.
    have x1_neq_x2: p1#x != p2#x
      by apply: add_finite_different_x.
    move: Hall_fin => /andP; elim=> Hfin_p1; move/andP; elim=> Hfin_p2 Hall_fin.
    have [x1 [y1 Hp1]] : exists x1 y1, p1 = (|x1, y1|)
      by apply: pointE.
    have [x2 [y2 Hp2]] : exists x2 y2, p2 = (|x2, y2|)
      by apply: pointE.
    have oncve_p2N: oncurve M (\-p2) by apply: MCGroup.negO.
    rewrite /p3 /p4 Hp1 Hp2 /=.
    rewrite ?Hp1 ?Hp2 in oncve_p1 oncve_p2 oncve_p2N x1_neq_x2.
    rewrite /MCGroup.add (negbTE x1_neq_x2) /=.
    clear Hp1 Hp2 Hall_fin Hfin_p1 Hfin_p2 p3 p4 p1_neq_p2 p1 p2.
    case: (boolP (x1 * x2 == 0)).
    * move=> x1_x2_eq0 {oncve_p2N}.
      wlog: x1 x2 y1 y2 oncve_p1 oncve_p2 x1_neq_x2 x1_x2_eq0 / x1 = 0.
        move: (x1_x2_eq0); rewrite mulf_eq0 =>/orP; case=>/eqP.
        + by move=> x1_eq0 -> //.
        + have ->: (((y2 - y1) / (x2 - x1))^+2 * M#b - M#a - x1 - x2) *
            (((- y2 - y1) / (x2 - x1))^+2 * M#b - M#a - x1 - x2) *
            (x1 - x2)^+2
            = (((y1 - y2) / (x1 - x2))^+2 * M#b - M#a - x2 - x1) *
            (((-y1 - y2) / (x1 - x2))^+2 * M#b - M#a - x2 - x1) *
            (x2 - x1)^+2
            by ssfield; rewrite subr_eq0 // eq_sym.
          rewrite [x1 * x2]mulrC => x2_eq0 -> //.
          - by rewrite eq_sym.
          - by rewrite mulrC.
      move=> x1_eq0.
      have x2_neq0: x2 != 0
        by apply/(@contra _ (x1 == x2)) => // /eqP->; rewrite x1_eq0.
      have ->: y1 = 0.
        apply/eqP; rewrite -sqrf_eq0 -(@mulrI_eq0 _ (M#b)); last first.
          apply/lregP; exact: mcu_b_neq0.
        apply/eqP; move: oncve_p1 x1_eq0 => /eqP-> ->.
        by rewrite !expr0n /= ?mulr0 !addr0.
      rewrite {}x1_eq0 !subr0 mul0r !sub0r mulNr !sqrrN expr1n.
      set a := _ - x2. rewrite -[a * a]/(a^+2) -exprMn {}/a.
      rewrite [_^+2 * M#b]mulrC [(y2 / x2)^+2]exprMn [M#b * _]mulrA.
      move: oncve_p2 =>/eqP->.
      by ssfield.
    * move=> x1_x2_neq0.
      apply/(@mulIf _ ((x1 - x2)^+2)).
        by rewrite expf_neq0 // subr_eq0.
      set x3 := _ - x1 - x2.
      set x4 := _ - x1 - x2.
      have ->: x3 * x4 * (x1 - x2)^+2 * (x1 - x2)^+2
        = (x3 * (x1 - x2)^+2) * (x4 * (x1 - x2)^+2) by ssring.
      rewrite {}/x3 {}/x4.
      have ->: (((y2 - y1) / (x2 - x1))^+2 * M#b - M#a - x1 - x2) * (x1 - x2)^+2
        = (M#b * y1^+2 - x1^+3 - M#a * x1^+2)
        + (M#b * y2^+2 - x2^+3 - M#a * x2^+2)
        - 2%:R * M#b * y1 * y2 + 2%:R * M#a * x1 * x2 + x1^+2 * x2 + x1 * x2^+2
        by ssfield; rewrite subr_eq0 eq_sym.
      have ->: (((-y2 - y1) / (x2 - x1))^+2 * M#b - M#a - x1 - x2) * (x1 - x2)^+2
        = (M#b * y1^+2 - x1^+3 - M#a * x1^+2)
        + (M#b * y2^+2 - x2^+3 - M#a * x2^+2)
        + 2%:R * M#b * y1 * y2 + 2%:R * M#a * x1 * x2 + x1^+2 * x2 + x1 * x2^+2
        by ssfield; rewrite subr_eq0 eq_sym.
      have ->: M#b * y1^+2 - x1^+3 - M#a * x1^+2 = x1
        by move: oncve_p1 => /eqP->; ssring.
      have ->: M#b * y2^+2 - x2^+3 - M#a * x2^+2 = x2
        by move: oncve_p2 => /eqP->; ssring.
      have ->: x1 + x2 - 2%:R * M#b * y1 * y2 + 2%:R * M#a * x1 * x2
        + x1^+2 * x2 + x1 * x2^+2
        = (x1^+2 * (x2^+3 + M#a * x2^+2 + x2)
          - 2%:R * M#b * x1 * x2 * y1 * y2
          + x2^+2 * (x1^+3 + M#a * x1^+2 + x1)) / (x1 * x2)
          by ssfield.
      have ->: x1 + x2 + 2%:R * M#b * y1 * y2 + 2%:R * M#a * x1 * x2
        + x1^+2 * x2 + x1 * x2^+2
        = (x1^+2 * (x2^+3 + M#a * x2^+2 + x2)
          + 2%:R * M#b * x1 * x2 * y1 * y2
          + x2^+2 * (x1^+3 + M#a * x1^+2 + x1)) / (x1 * x2)
          by ssfield.
      have ->: x1^+3 + M#a * x1^+2 + x1 = M#b * y1^+2
        by move: oncve_p1 => /eqP->.
      have ->: x2^+3 + M#a * x2^+2 + x2 = M#b * y2^+2
        by move: oncve_p2 => /eqP->.
      have ->: x1^+2 * (M#b * y2^+2)
        - 2%:R * M#b * x1 * x2 * y1 * y2
        + x2^+2 * (M#b * y1^+2)
        = M#b * (x1 * y2 - x2 * y1)^+2
        by ssring.
      have ->: x1^+2 * (M#b * y2^+2)
        + 2%:R * M#b * x1 * x2 * y1 * y2
        + x2^+2 * (M#b * y1^+2)
        = M#b * (x1 * y2 + x2 * y1)^+2
        by ssring.
      have ->: M#b * (x1 * y2 - x2 * y1) ^+ 2 / (x1 * x2)
        * (M#b * (x1 * y2 + x2 * y1) ^+ 2 / (x1 * x2))
        = (x1^+2 * (M#b * y2^+2) - x2^+2 * (M#b * y1^+2))^+2 / (x1 * x2)^+2
        by ssfield; rewrite ?expf_neq0 //.
      have ->: M#b * y1^+2 = x1^+3 + M#a * x1^+2 + x1
        by move: oncve_p1 => /eqP->.
      have ->: M#b * y2^+2 = x2^+3 + M#a * x2^+2 + x2
        by move: oncve_p2 => /eqP->.
      by ssfield; rewrite ?expf_neq0 //.
  Qed.

  Lemma montgomery_eq : oncurve M p1 -> p1 = p2 ->
    all point_is_fin [:: p1; p3] ->
    4%:R * p1#x * p3#x * (p1#x^+2 + M#a * p1#x + 1) = (p1#x ^+2 - 1)^+2.
  Proof.
    move=> oncve_p1 p1_eq_p2.
    move/andP; elim=> Hfin_p1; move/andP; elim=> Hfin_p3 _.
    have [x1 [y1 Hp1]]: exists x1 y1, p1 = (|x1, y1|)
      by apply: pointE.
    clear Hfin_p1.
    rewrite /p3 -p1_eq_p2 Hp1.
    have y1_neq0: y1 != 0.
      apply/(@contraL _ (point_is_fin p3)) => [y1_eq0|]; last by [].
      by rewrite /p3 -p1_eq_p2 /MCGroup.add Hp1 !eq_refl y1_eq0.
    rewrite {}Hp1 in oncve_p1.
    rewrite /MCGroup.add !eq_refl y1_neq0 /=.
    set c := (_ / _)^+2.
    rewrite -[4%:R * x1 * _]mulrA [x1 * _]mulrC -2!mulrA.
    have ->: x1 * (x1^+2 + M#a * x1 + 1) = x1^+3 + M#a * x1^+2 + x1 by ssring.
    move: (oncve_p1) => /eqP<-.
    have ->: (x1^+2 - 1)^+2 =
      (3%:R * x1^+2 + 2%:R * M#a * x1 + 1)^+2 -
      4%:R * (x1^+3 + M#a * x1^+2 + x1) * (M#a + 2%:R * x1) by ssring.
    move: (oncve_p1) => /eqP<-.
    rewrite {}/c.
    by ssfield; rewrite !mulf_neq0 // ?ecu_chi2 // mcu_b_neq0.
  Qed.
End MontgomerysFormulas.

Ltac oncurves := match goal with 
  | _ => apply MCGroup.negO => //
  | _ => done
  | _ => idtac
  end.

Section MontgomerysHomFormulas.
  Variable K : ecuFieldType.
  Variable M : mcuType K.

  Local Notation "\- x"   := (@MCGroup.neg _ x).
  Local Notation "x \+ y" := (@MCGroup.add _ M x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Inductive K_infty :=
  | K_Inf : K_infty
  | K_Fin : K -> K_infty.
  Definition K_infty_eq (x y : K_infty) :=
    match x, y with
    | K_Inf   , K_Inf    => true
    | K_Fin x', K_Fin y' => (x' == y')
    | _       , _        => false
    end.
  Lemma K_infty_eqP :
    forall (x y : K_infty), reflect (x = y) (K_infty_eq x y).
  Proof.
    move=> x y; apply: (iffP idP).
    + by move: x y => [|x'] [|y'] //= /eqP->.
    + by move=> {y} <-; case: x => //= *; rewrite !eqxx.
  Qed.
  Definition K_infty_eqMixin := EqMixin K_infty_eqP.
  Canonical Structure K_infty_eqType :=
    Eval hnf in (EqType _ K_infty_eqMixin).

  Definition point_x (p : point K) :=
    if p is (|x, _|) then K_Fin x else K_Inf.
  Local Notation "p '#x'" := (point_x p) (at level 30).
  Local Notation "p '#x0'" := (point_x0 p) (at level 30).

  Lemma point_x_neg (p : point K) : (\- p)#x = p#x.
  Proof. by case: p. Qed.

  Lemma point_x0_neq0_fin (p : point K) : p#x0 != 0 -> point_is_fin p.
  Proof. by case: p; first by rewrite eq_refl. Qed.

  Lemma point_x_K_Fin_point_x0 (p : point K) :
    point_is_fin p -> p#x = K_Fin (p#x0).
  Proof. by case: p. Qed.

  Definition inf_div (x z : K) := (* TODO: better name? *)
    if z == 0 then K_Inf else K_Fin (x / z).
  Lemma inf_div_K_Inf (x z : K) : (inf_div x z == K_Inf) = (z == 0).
  Proof. by rewrite /inf_div; case: ifP. Qed.
  Lemma inf_div_K_Fin (x z x' : K) : inf_div x z = K_Fin x' -> z != 0.
  Proof. by rewrite /inf_div; case: ifP. Qed.

  Lemma inf_div_eq0 (x z : K) : z != 0 -> (inf_div x z == K_Fin 0) = (x == 0).
  Proof.
    move=> z_neq0.
    apply/eqP/eqP => [|->]; rewrite /inf_div (negbTE z_neq0).
    + by case => /eqP; rewrite -(inj_eq (mulIf z_neq0)) mulfVK // mul0r => /eqP.
    + by rewrite mul0r.
  Qed.

  Lemma point_x0_point_x x z p : z != 0 -> point_is_fin p ->
    (p#x0 == x / z) = (p#x == inf_div x z).
  Proof.
    case: p; first by [].
    move=> p_x p_y z_neq_0 Hp_fin.
    rewrite /inf_div (negbTE z_neq_0) /=.
    apply/eqP/idP; first by move->.
    by move/eqP; case.
  Qed.

  Lemma point_x0_neq0_point_x x z p : p#x0 != 0 ->
    p#x = inf_div x z -> p#x0 = x / z.
  Proof.
    move=> Hneq0 Hp.
    apply/eqP; rewrite point_x0_point_x; first by apply/eqP.
    + apply: contra_neq; last by exact: Hneq0.
      move=> z_eq0 {Hneq0}; case: p Hp; first by [].
      move=> k _ /= H.
      have z_neq0 : z != 0 by apply: inf_div_K_Fin; apply/sym_eq; exact: H.
      by have : false by apply: contra_eqT => [_|]; first by exact: z_neq0.
    + by case: p Hneq0 Hp; first by rewrite eq_refl.
  Qed.

  Definition hom_ok (x z : K) := (x != 0) || (z != 0).

  Variables x1 x2 x4 z1 z2 z4 : K.

  Lemma not_opposite_points_add_finite p1_x p1_y p2_x p2_y :
    let p1 := (|p1_x, p1_y|) in
    let p2 := (|p2_x, p2_y|) in
    oncurve M p1 -> oncurve M p2 -> p1 != p2 -> p1 != \- p2 ->
    point_is_fin (p1 \+ p2).
  Proof.
    move=> p1 p2 oncve_p1 oncve_p2 p1_neq_p2 p1_neq_p2N.
    suff : (p1 \+ p2 != ∞) by case: (p1 \+ p2).
    rewrite /MCGroup.add /=.
    case: (boolP (p1_x == p2_x)) => // /eqP p1x_eq_p2x.
    move: p1_neq_p2N.
    have -> : p1 = \- p2 by apply: (same_x_opposite_points (M:=M)).
    by rewrite eq_refl.
  Qed.

  Lemma not_opposite_points_different_x p1_x p1_y p2_x p2_y :
    let p1 := (|p1_x, p1_y|) in
    let p2 := (|p2_x, p2_y|) in
    oncurve M p1 -> oncurve M p2 -> p1 != p2 -> p1 != \- p2 -> p1#x != p2#x.
  Proof.
    move=> p1 p2 oncve_p1 oncve_p2 p1_neq_p2 p1_neq_p2N.
    pose p3 := p1 \+ p2.
    have p3_fin : point_is_fin p3 by apply: not_opposite_points_add_finite.
    have Hall_fin : all (@point_is_fin K) [:: p1; p2; p3] by rewrite /= p3_fin.
    rewrite eqE /= -[p1_x]/(point_x0 p1) -[p2_x]/(point_x0 p2).
    by apply: (add_finite_different_x (M:=M)).
  Qed.

  Hypothesis mcu_no_square : forall x : K, x^+2 != (M#a)^+2 - 4%:R.
  Lemma aux_no_square x : x != 0 -> x^+2 + M#a * x + 1 != 0. (* TODO: better name *)
  Proof.
    move=> x_neq_0; apply: contraT.
    rewrite negbK -(inj_eq (addrI (-x^+2))) -(inj_eq (subIr 1)).
    rewrite -[_ + 1]addrA addKr addrK addr0.
    rewrite -(inj_eq (@divIf _ x _)) // mulfK //.
    move/eqP/(congr1 (fun x => x^+2))/eqP.
    rewrite -(inj_eq (subIr 4%:R)).
    have -> : ((-x^+2 - 1) / x) ^+ 2 - 4%:R = (x - 1/x)^+2 by ssfield.
    by rewrite eq_sym (negbTE (mcu_no_square _)).
  Qed.

  Lemma point_x_eq0_point_y_eq0 p_x p_y :
    let p := (|p_x, p_y|) in
    oncurve M p -> (p_x == 0) = (p_y == 0).
  Proof.
    move=> p oncve_p; apply/eqP/eqP.
    + move=> p_x_eq0; move: oncve_p.
      rewrite /oncurve /p p_x_eq0 !expr0n /= mulr0 !addr0.
      by rewrite mulf_eq0 (negbTE (mcu_b_neq0 M)) sqrf_eq0 /= => /eqP.
    + move=> p_y_eq0; move: oncve_p.
      rewrite /oncurve /p p_y_eq0 expr0n mulr0 eq_sym => /eqP.
      apply: contra_eq => p_x_neq0.
      rewrite exprS expr2 !mulrA -{6}[p_x]mul1r -2!mulrDl -expr2 mulf_neq0 //.
      by apply: aux_no_square.
  Qed.

  Lemma point_x_neq0_double_finite p_x p_y :
    let p := (|p_x, p_y|) in
    oncurve M p -> p_x != 0 -> point_is_fin (p \+ p).
  Proof.
    move=> p oncve_p p_x_neq0.
    rewrite /p /MCGroup.add !eq_refl.
    by rewrite -(@point_x_eq0_point_y_eq0 p_x) // p_x_neq0.
  Qed.

  Lemma montgomery_hom_neq :
    hom_ok x1 z1 -> hom_ok x2 z2 -> (x4 != 0) && (z4 != 0) ->
    let x3 := z4 * ((x1 - z1)*(x2 + z2) + (x1 + z1)*(x2 - z2))^+2 in
    let z3 := x4 * ((x1 - z1)*(x2 + z2) - (x1 + z1)*(x2 - z2))^+2 in
    forall p1 p2 : point K,
    oncurve M p1 -> oncurve M p2 ->
    p1#x = inf_div x1 z1 ->
    p2#x = inf_div x2 z2 ->
    (p1 \- p2)#x = inf_div x4 z4 ->
    hom_ok x3 z3 && ((p1 \+ p2)#x == inf_div x3 z3).
  Proof.
    move=> H1_ok H2_ok /andP [x4_neq_0 z4_neq_0] x3 z3 p1 p2 oncve_p1 oncve_p2.
    move=> Hp1x Hp2x Hp4x.
    case: (boolP (p1 == p2)) => [/eqP p1_eq_p2 | p1_neq_p2].
      move: Hp4x.
      rewrite p1_eq_p2 MCGroup.addoC ; oncurves => /=.
      rewrite MCGroup.addNo; oncurves => /= => /eqP.
      by rewrite eq_sym inf_div_K_Inf (negbTE z4_neq_0).
    case: p1 => [| p1_x p1_y] in oncve_p1 Hp1x Hp4x p1_neq_p2 *.
      move: Hp1x => /eqP; rewrite eq_sym inf_div_K_Inf => /eqP z1_eq_0.
      have x1_neq_0 : x1 != 0
        by move: z1_eq_0 H1_ok => -> /orP; elim; rewrite ?eq_refl.
      move: Hp4x.
      rewrite MCGroup.add0o ?point_x_neg; last by apply: MCGroup.negO.
      rewrite Hp2x /inf_div (negbTE z4_neq_0).
      case: ifP => [| /negbT z2_neq_0]; first by [].
      case; rewrite -[x4 / z4](mulfK z2_neq_0) => /(divIf z2_neq_0) Hx2.
      have x2_neq_0 : x2 != 0 by rewrite Hx2 !mulf_neq0 // invr_neq0 //.
      have z3_neq_0 : z3 != 0.
        rewrite /z3 mulf_neq0 // sqrf_eq0 z1_eq_0.
        rewrite addr0 subr0 -mulrN -mulrDr opprB addrC addrA.
        rewrite -[_ + x2]addrA addNr addr0.
        apply: mulf_neq0; first by [].
        by rewrite -mulr2n -mulr_natl mulf_neq0 ?ecu_chi2.
      rewrite /hom_ok z3_neq_0 orbT /=.
      have ->:(z3 == 0 = false).
      apply/eqP; move/eqP: z3_neq_0 => //.
      apply/eqP; apply: congr1.
      rewrite /x3 /z3 Hx2 z1_eq_0 !addr0 !subr0.
      rewrite -mulrN -!mulrDr opprB {1}[_ - z2]addrC [_ + (z2 - _)]addrC.
      rewrite !addrA -[_ - z2]addrA -[X in X + z2]addrA addrN addNr !addr0.
      by ssfield; rewrite ?mulf_neq0 // -mulr2n -mulr_natl mulf_neq0 ?ecu_chi2.
    case: p2 => [| p2_x p2_y] in oncve_p2 Hp2x Hp4x p1_neq_p2 *.
      move: Hp2x => /eqP; rewrite eq_sym inf_div_K_Inf => /eqP z2_eq_0.
      have x2_neq_0 : x2 != 0
        by move: z2_eq_0 H2_ok => -> /orP; elim; rewrite ?eq_refl.
      move: Hp4x.
      rewrite /MCGroup.add /=.
      rewrite /= in Hp1x.
      rewrite Hp1x {1 2}/inf_div (negbTE z4_neq_0).
      case: ifP => [| /negbT z1_neq_0]; first by [].
      case; rewrite -[x4 / z4](mulfK z1_neq_0) => /(divIf z1_neq_0) Hx1.
      have x1_neq_0 : x1 != 0 by rewrite Hx1 !mulf_neq0 // invr_neq0 //.
      have z3_neq_0 : z3 != 0.
        rewrite /z3 mulf_neq0 // sqrf_eq0 z2_eq_0.
        rewrite addr0 subr0 -mulNr -mulrDl opprD [x1 - _]addrC addrA.
        rewrite -[_ - x1]addrA subrr addr0 -opprD.
        apply: mulf_neq0; last by [].
        by rewrite oppr_eq0 -mulr2n -mulr_natl mulf_neq0 ?ecu_chi2.
      rewrite /hom_ok z3_neq_0 orbT /=.
      rewrite /inf_div (negbTE z1_neq_0) (negbTE z3_neq_0).
      apply/eqP; apply: congr1.
      rewrite /x3 /z3 Hx1 z2_eq_0 !addr0 !subr0.
      rewrite -mulNr -!mulrDl opprD [_ + z1]addrC {2}[_ - z1]addrC.
      rewrite !addrA -[_ + z1]addrA -[X in X - z1]addrA addrN addNr !addr0.
      ssfield; rewrite //.
      rewrite mulf_neq0 // sqrf_eq0 -mulr2n -mulr_natl.
      by rewrite !mulf_neq0 ?oppr_eq0 ?ecu_chi2.
    case: (boolP ((|p1_x, p1_y|) == (|p2_x, -p2_y|))) => [/eqP H | p1_neq_Np2].
      rewrite H in Hp1x *.
      rewrite /= in Hp1x Hp2x.
      rewrite -[(|p2_x, (- p2_y)|)]/(\- (|p2_x, p2_y|)) MCGroup.addNo ; oncurves => /=.
      have z1_neq_0 : z1 != 0 by apply/inf_div_K_Fin/sym_eq; exact Hp1x.
      have z2_neq_0 : z2 != 0 by apply/inf_div_K_Fin/sym_eq; exact Hp2x.
      have Hx1 : x1 = x2 / z2 * z1.
        apply/(@divIf _ z1); first by [].
        rewrite -[_ * z1 / z1]mulrA divff // mulr1.
        move: Hp1x Hp2x; rewrite /inf_div (negbTE z1_neq_0) (negbTE z2_neq_0).
        by case => ->; case.
      have p2_x_neq0 : p2_x != 0.
        apply: contra p1_neq_p2 => p2_x_eq0.
        have p2_y_eq0 : p2_y == 0 by rewrite -(@point_x_eq0_point_y_eq0 p2_x).
        by rewrite H; move: p2_x_eq0 p2_y_eq0 => /eqP-> /eqP->; rewrite oppr0.
      have z3_eq0 : z3 = 0 by rewrite /z3 Hx1; ssfield.
      have x3_neq0 : x3 != 0.
        apply: contra_neq (x4_neq_0) => x3_eq0.
        apply/eqP; rewrite -(@inf_div_eq0 _ z4) // -Hp4x H.
        apply/eqP.
        set p2N := (|p2_x, (- p2_y)|).
        have oncve_p2N : oncurve M p2N by rewrite MCGroup.oncurveN /= opprK.
        have p2Ndouble_is_fin : point_is_fin (p2N \+ p2N).
          by apply: point_x_neq0_double_finite.
        rewrite point_x_K_Fin_point_x0 //.
        congr K_Fin.
        apply/(@mulfI _ (4%:R * p2N#x0)).
          by rewrite mulf_neq0 // (@natrX _ 2 2) sqrf_eq0 ecu_chi2.
        apply/(@mulIf _ (p2N#x0^+2 + M#a * p2N#x0 + 1)).
          by apply: aux_no_square.
        rewrite mulr0 mul0r montgomery_eq //= ?p2Ndouble_is_fin //.
        apply/eqP; rewrite sqrf_eq0 subr_eq0 sqrf_eq1.
        move/eqP: Hp2x; rewrite -[_ p2_x]/(p2N#x) -point_x0_point_x//= =>/eqP->.
        rewrite -(inj_eq (@mulIf _ z2 _)) // -[_==-1](inj_eq (@mulIf _ z2 _))//.
        rewrite mulfVK // mul1r mulN1r.
        move/eqP: x3_eq0; rewrite /x3 mulf_eq0 (negbTE z4_neq_0) sqrf_eq0.
        move/eqP: z3_eq0; rewrite /z3 mulf_eq0 (negbTE x4_neq_0) sqrf_eq0.
        move => /= /eqP H_eq0_1 /eqP H_eq0_2.
        have : (x1 - z1) * (x2 + z2) = 0.
          apply/(@mulfI _ 2%:R); first by exact: ecu_chi2.
          rewrite mulr0 mulr_natl mulr2n -H_eq0_1; apply/(congr1 (+%R _)).
          by apply/eqP; rewrite -addr_eq0; apply/eqP.
        have : (x1 + z1) * (x2 - z2) = 0.
          apply/(@mulfI _ 2%:R); first by exact: ecu_chi2.
          rewrite mulr0 mulr_natl mulr2n -H_eq0_2; apply/(congr1 (+%R^~ _)).
          by apply/esym/eqP; rewrite -subr_eq0; apply/eqP.
        case: (boolP (x1 == z1)) => [/eqP->|].
        + move/eqP. rewrite -mulr2n mulf_eq0 -mulr_natl.
          have /negbTE-> : (2%:R * z1 != 0) by rewrite mulf_neq0 // ecu_chi2.
          by rewrite subr_eq0 /= => ->.
        + rewrite -subr_eq0 => Htmp _ /eqP.
          by rewrite mulf_eq0 (negbTE Htmp) addr_eq0 /= => ->; rewrite orbT.
      by rewrite /hom_ok x3_neq0 /= eq_sym inf_div_K_Inf z3_eq0 eq_refl.
    set p1 := (|p1_x, p1_y|) in oncve_p1 Hp1x Hp4x p1_neq_p2 p1_neq_Np2 *.
    rewrite -[(|p2_x, (- p2_y)|)]/(\- (|p2_x, p2_y|)) in p1_neq_Np2.
    set p2 := (|p2_x, p2_y|) in oncve_p2 Hp2x Hp4x p1_neq_p2 p1_neq_Np2 *.
    set p3 := p1 \+ p2.
    set p4 := p1 \- p2 in Hp4x.
    have z1_neq_0 : z1 != 0 by apply/inf_div_K_Fin/sym_eq; exact Hp1x.
    have z2_neq_0 : z2 != 0 by apply/inf_div_K_Fin/sym_eq; exact Hp2x.
    have z3_neq_0 : z3 != 0.
      rewrite /z3 mulf_neq0 // sqrf_eq0.
      have -> : (x1 - z1) * (x2 + z2) - (x1 + z1) * (x2 - z2)
        = 2%:R * (x1*z2 - x2*z1) by ssring.
      rewrite mulf_neq0 // ?ecu_chi2 // subr_eq0.
      rewrite -(inj_eq (@divIf _ z2 _)) // mulfK //.
      apply: contraT => /negbNE/eqP Hx1.
      have : p1#x != p2#x by apply: not_opposite_points_different_x.
      move: Hp1x => /eqP; rewrite -point_x0_point_x // Hx1 mulrAC mulfK //.
      move: Hp2x => /eqP; rewrite -point_x0_point_x // => /eqP <- /= /eqP ->.
      by rewrite eq_refl.
    rewrite /hom_ok z3_neq_0 orbT /=.
    have p3_fin : point_is_fin p3 by apply: not_opposite_points_add_finite.
    have p4_fin : point_is_fin p4.
      apply: not_opposite_points_add_finite; rewrite -/(\-(|p2_x, _|)) //.
      + by apply: MCGroup.negO.
      + by rewrite /= opprK.
    rewrite -point_x0_point_x //; apply/eqP.
    apply/(@mulIf _ ((point_x0 p4) * ((point_x0 p1) - (point_x0 p2))^+2)).
      rewrite mulf_neq0 //=.
      + move: Hp4x => /eqP; rewrite -point_x0_point_x // => /eqP->.
        by rewrite mulf_neq0 // invr_neq0.
      + rewrite sqrf_eq0 subr_eq0.
        by apply: (@not_opposite_points_different_x _ p1_y _ p2_y).
    have Hall_fin : all (@point_is_fin K) [:: p1; p2; p3] by rewrite /= p3_fin.
    rewrite mulrA montgomery_neq //.
    move: Hp1x => /eqP; rewrite -point_x0_point_x // => /eqP->.
    move: Hp2x => /eqP; rewrite -point_x0_point_x // => /eqP->.
    move: Hp4x => /eqP; rewrite -point_x0_point_x // => /eqP->.
    by rewrite /x3 /z3; ssfield.
  Qed.

  Lemma montgomery_hom_eq_ok :
    hom_ok x1 z1 ->
    let x1z1_4 := (x1 + z1)^+2 - (x1 - z1)^+2 in
    let x3 := (x1 + z1)^+2 * (x1 - z1)^+2 in
    let z3 := x1z1_4 * ((x1 + z1)^+2 + ((M#a - 2%:R)/4%:R) * x1z1_4) in
    hom_ok x3 z3.
  Proof.
    move=> Hok /=.
    set x3 := (X in hom_ok X _).
    set z3 := (X in hom_ok _ X).
    rewrite /hom_ok.
    case: (boolP (x3 == 0)); last by [].
    rewrite orFb => x3_eq0.
    have H4_neq0 : 4%:R != 0 :> K by rewrite (@natrX _ 2 2) sqrf_eq0 ecu_chi2.
    have H1 : (x1 == z1) || (x1 == -z1).
      by rewrite -eqf_sqr -subr_eq0 subr_sqr -sqrf_eq0 exprMn mulrC.
    have z1_neq0 : z1 != 0.
      case/orP: Hok; last by [].
      by case/orP: H1 => /eqP->; rewrite ?oppr_eq0.
    have x1_neq0 : x1 != 0.
      by case/orP: H1 => /eqP->; rewrite ?oppr_eq0.
    apply: mulf_neq0; first by rewrite subr_sqrDB -mulr_natr !mulf_neq0 //.
    set lhs := (X in X != 0).
    have {lhs} -> : lhs = M#a * (x1 * z1) + (x1^+2 + z1^+2) by ssfield.
    case/orP: H1 => /eqP->.
    + rewrite -mulr2n -mulr_natl -expr2 -mulrDl mulf_neq0 ?sqrf_eq0 // addr_eq0.
      apply: contraNneq (mcu_asq_neq4 M) => /(congr1 (fun x => x^+2)).
      by rewrite sqrrN -natrX => /eqP.
    + rewrite mulNr mulrN sqrrN addrC -mulr2n -mulr_natl -expr2 -mulrBl.
      rewrite mulf_neq0 ?sqrf_eq0 // subr_eq0 eq_sym.
      apply: contraNneq (mcu_asq_neq4 M) => /(congr1 (fun x => x^+2)).
      by rewrite -natrX => /eqP.
  Qed.

  Lemma montgomery_hom_eq :
    hom_ok x1 z1 ->
    let x1z1_4 := (x1 + z1)^+2 - (x1 - z1)^+2 in
    let x3 := (x1 + z1)^+2 * (x1 - z1)^+2 in
    let z3 := x1z1_4 * ((x1 + z1)^+2 + ((M#a - 2%:R)/4%:R) * x1z1_4) in
    forall p : point K, oncurve M p ->
    p#x = inf_div x1 z1 ->
    (p \+ p)#x = inf_div x3 z3.
  Proof. (* TODO: use montgomery_hom_eq_ok? *)
    move=> H1_ok x1z1_4 x3 z3 p oncve_p Hpx.
    case: p => [| p_x p_y] in oncve_p Hpx *.
      move: Hpx => /eqP; rewrite eq_sym inf_div_K_Inf => /eqP z1_eq_0.
      have x1z1_4_eq_0 : x1z1_4 = 0
        by rewrite /x1z1_4 z1_eq_0 addr0 subr0 subrr.
      have /eqP : z3 = 0 by rewrite /z3 x1z1_4_eq_0 mul0r.
      by rewrite -(inf_div_K_Inf x3) => /eqP ->.
    have z1_neq_0 : z1 != 0 by apply/inf_div_K_Fin/sym_eq; exact Hpx.
    set p := (|p_x, p_y|) in oncve_p Hpx *.
    move: Hpx => /eqP; rewrite -point_x0_point_x //= => /eqP Hpx.
    case: (boolP (x1 == 0)) => [/eqP x1_eq_0 | x1_neq_0].
      have p_eq_0 : p = (|0, 0|).
        have px_eq_0 : p_x = 0 by rewrite Hpx x1_eq_0 mul0r.
        move: oncve_p.
        rewrite /p px_eq_0 /oncurve !expr0n /= mulr0 !addr0 mulf_eq0.
        by rewrite (negbTE (mcu_b_neq0 _)) orFb sqrf_eq0 => /eqP ->.
      inversion p_eq_0.
      rewrite {}p_eq_0 in oncve_p Hpx *.
      rewrite !eq_refl /=.
      have x1z1_4_eq_0 : x1z1_4 = 0.
        by rewrite /x1z1_4 x1_eq_0 add0r sub0r sqrrN subrr.
      have /eqP : z3 = 0 by rewrite /z3 x1z1_4_eq_0 mul0r.
      by rewrite -(inf_div_K_Inf x3) => /eqP ->.
    have H4_neq_0 : (4%:R : K) != 0 by rewrite (@natrX _ 2 2) sqrf_eq0 ecu_chi2.
    have z3_neq_0 : z3 != 0.
      have Hx1z1_4 : x1z1_4 = 4%:R * x1 * z1 by ssring.
      have x1z1_4_neq_0 : x1z1_4 != 0
        by rewrite Hx1z1_4 !mulf_neq0 //.
      rewrite /z3 !mulf_neq0 // Hx1z1_4.
      have -> : (x1 + z1)^+2 + (M#a - 2%:R) / 4%:R * (4%:R * x1 * z1)
        = x1^+2 + M#a * x1 * z1 + z1^+2.
        rewrite !mulrA mulfVK //.
        by ssring.
      rewrite -(inj_eq (@divIf _ (z1^+2) _)) ?sqrf_eq0 // mul0r.
      rewrite !mulrDl divff ?sqrf_eq0 // -exprVn -exprMn.
      rewrite [z1^-1^+2]expr2 mulrA mulfK // -mulrA.
      by apply: aux_no_square; rewrite mulf_neq0 // invr_neq0.
    have px_neq_0 : p_x != 0 by rewrite Hpx mulf_neq0 // invr_neq0.
    have py_neq_0 : p_y != 0.
      rewrite -sqrf_eq0 -(inj_eq (@mulfI _ (M#b) _)) ?mcu_b_neq0 // mulr0.
      move: oncve_p; rewrite /oncurve /p => /eqP ->.
      have -> : p_x^+3 + M #a * p_x^+2 + p_x = p_x * (p_x^+2 + M #a * p_x + 1)
        by ssring.
      by rewrite mulf_neq0 // aux_no_square.
    have pDp_fin : point_is_fin (p \+ p).
      by rewrite /MCGroup.add /p !eq_refl py_neq_0.
    apply/eqP; rewrite -point_x0_point_x //; apply/eqP.
    rewrite !eq_refl py_neq_0 /=.
    have Hall_fin : all (@point_is_fin K) [:: p; p \+ p] by rewrite /= pDp_fin.
    apply/(@mulfI _ (4%:R * (point_x0 p))); first by rewrite mulf_neq0 //.
    apply/(@mulIf _ ((point_x0 p)^+2 + M#a * (point_x0 p) + 1)).
      by apply: aux_no_square.
    apply/(@mulIf _ z3); first by [].
    rewrite -[_ * z3 in RHS]mulrA [_ * z3 in RHS]mulrC [_ * (z3 * _)]mulrA.
    rewrite [_ * (x3 / z3)]mulrA mulfVK //.
    have Hp: p = p => //.
    have Hp2: p = (|p_x, p_y|) => //.
    have := montgomery_eq oncve_p Hp Hall_fin.
      rewrite /MCGroup.add Hp2 !eq_refl py_neq_0 /=.
    move=>->.
    rewrite Hpx /x3 /z3 /x1z1_4.
    by ssfield.
  Qed.
End MontgomerysHomFormulas.