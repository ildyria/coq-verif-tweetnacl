Set Warnings "-notation-overridden,-parsing".
From mathcomp Require Import ssreflect ssrnat ssrbool eqtype fintype.
From mathcomp Require Import tuple seq fintype bigop ssralg finalg.
From mathcomp Require Import ssrfun choice zmodp fingroup.
From SsrMultinomials Require Import mpoly.
From SsrEllipticCurves Require Import polyall polydec ssrring ecgroup ec.
From Tweetnacl.High Require Import mc.

Import GRing.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Section MCEC.
  Variable K : ecuFieldType.
  Variable M : mcuType K.

  Lemma ecuType_of_mcuType_discriminant_ok :
    let: a' := (3%:R - (M#a)^+2) / (3%:R * (M#b)^+2) in
    let: b' := (2%:R * (M#a)^+3 - 9%:R * (M#a)) / (27%:R * (M#b)^+3) in
    4%:R * a' ^+ 3 + 27%:R * b' ^+ 2 != 0.
  Proof.
    move: (ecu_chi3 K) (mcu_b_neq0 M) (mcu_asq_neq4 M) => ? ? ?.
    have ->: 4%:R * ((3%:R - (M#a)^+2) / (3%:R * (M#b)^+2))^+3
      + 27%:R * ((2%:R * (M#a) ^+ 3 - 9%:R * M#a) / (27%:R * (M#b)^+3))^+2
      = -((M#a)^+2 - 4%:R) / (M#b)^+6.
      by ssfield; rewrite ?mulf_neq0 ?(@natrX _ 3 3) ?expf_neq0 //.
    by rewrite mulf_neq0 ?oppr_eq0 ?subr_eq0 ?invr_neq0 ?expf_neq0 //.
  Qed.

  Definition ecuType_of_mcuType :=
    let: a' := (3%:R - M#a^+2) / (3%:R * M#b^+2) in
    let: b' := (2%:R * M#a^+3 - 9%:R * M#a) / (27%:R * M#b^+3) in
    (@Build_ecuType K a' b' ecuType_of_mcuType_discriminant_ok).

  Local Notation E := (ecuType_of_mcuType).

  Definition ec_of_mc_point p :=
    match p with
    | ∞ => ∞
    | (|x, y|) => (|x / (M#b) + (M#a) / (3%:R * (M#b)), y / (M#b)|)
    end.

  Lemma ec_of_mc_point_ok p : oncurve M p -> ec.oncurve E (ec_of_mc_point p).
  Proof.
    case: p => //= x y /eqP oc_p.
    have bcube_27_neq0: 27%:R * M#b^+3 != 0.
      apply: mulf_neq0.
      + by rewrite (@natrX _ 3 3) expf_neq0 //; exact: ecu_chi3.
      + by apply: expf_neq0; exact: mcu_b_neq0.
    rewrite addf_div ?mulf_neq0 ?ecu_chi3 ?mcu_b_neq0 // [M#b * _]mulrCA.
    rewrite [x * _]mulrCA mulrA -mulrDl {1 3}mulrCA invfM mulrA.
    rewrite mulfK ?mcu_b_neq0 // [_^+3]expr_div_n [(_*M#b)^+3]exprMn -natrX.
    rewrite mulf_div [_*(3%:R*_)]mulrACA -exprSr -natrM.
    rewrite -[X in _ + X /_ + _](@mulfK _ 3%:R) ?ecu_chi3 // -[_/3%:R/_]mulrA.
    rewrite -invfM [3%:R*(_*_^+3)]mulrA -natrM expnE /= !mulnE /= -!mulrDl.
    apply/eqP/(@mulIf _ (27%:R * M#b^+3)); first by exact: bcube_27_neq0.
    rewrite mulfVK ?bcube_27_neq0 //.
    rewrite mulrCA expr_div_n mulrAC -mulrA -expfB // expr1 [y^+2*_]mulrC oc_p.
    by rewrite !mulr_natr; ssring.
  Qed.

  Definition ec_of_mc p := EC (ec_of_mc_point_ok [oc of p]).

  Definition mc_of_ec_point p :=
    match p with
    | ∞ => ∞
    | (|x, y|) => (|M#b * (x - M#a / (3%:R * M#b)), M#b * y|)
    end.

  Lemma mc_of_ec_point_ok p : ec.oncurve E p -> oncurve M (mc_of_ec_point p).
  Proof.
    case: p => //= x y /eqP H.
    pose neq0 := (mulf_neq0, expf_neq0, @natrX _ 3 3, ecu_chi3, mcu_b_neq0).
    by rewrite exprMn H; apply/eqP; ssfield; rewrite !neq0.
  Qed.

  Definition mc_of_ec p := MC (mc_of_ec_point_ok (oncurve_ec p)).

  Lemma ec_of_mc_pointK : cancel ec_of_mc_point mc_of_ec_point.
  Proof.
    move=> [|x y] //.
    by congr (|_, _|); ssfield; rewrite ?mulf_neq0 ?ecu_chi3 ?mcu_b_neq0.
  Qed.

  Lemma mc_of_ec_pointK : cancel mc_of_ec_point ec_of_mc_point.
  Proof.
    move=> [|x y] //.
    by congr (|_, _|); ssfield; rewrite ?mulf_neq0 ?ecu_chi3 ?mcu_b_neq0.
  Qed.

  Lemma ec_of_mcK : cancel ec_of_mc mc_of_ec.
  Proof.
    move=> x; apply/eqP; rewrite eqE /=; apply/eqP.
    by exact: ec_of_mc_pointK.
  Qed.

  Lemma mc_of_ecK : cancel mc_of_ec ec_of_mc.
  Proof.
    move=> x; apply/eqP; rewrite eqE /=; apply/eqP.
    by exact: mc_of_ec_pointK.
  Qed.

  Lemma ec_of_mc_bij : bijective ec_of_mc.
  Proof. by exists mc_of_ec; [exact: ec_of_mcK|exact: mc_of_ecK]. Qed.

  Local Notation "x \+ y" := (@MCGroup.addmc _ M x y).

  Lemma ec_of_mc_pointD : forall p q, oncurve M p -> oncurve M q ->
    ec_of_mc_point (MCGroup.add M p q) = ECGroup.add E (ec_of_mc_point p) (ec_of_mc_point q).
  Proof.
    move=> [|x1 y1] [|x2 y2] oncve_p oncve_q //.
    + rewrite MCGroup.add0o // ECGroup.add0o //.
      by apply: ec_of_mc_point_ok.
    + rewrite ECGroup.addoC MCGroup.addoC MCGroup.add0o // ECGroup.add0o //.
      by apply: ec_of_mc_point_ok.
    + rewrite /MCGroup.add /ECGroup.add oncve_p oncve_q.
      rewrite !ec_of_mc_point_ok //=.
      rewrite (inj_eq (addIr _)) !(inj_eq (divIf _)) ?mcu_b_neq0 //.
      rewrite mulf_eq0 invr_eq0 (negbTE (mcu_b_neq0 M)) orbF.
      pose neq0 := (mulf_neq0, expf_neq0, ecu_chi2, ecu_chi3, mcu_b_neq0).
      case: ifP => [x1_eq_x2|/negbT x1_neq_x2].
      * case: ifP => // /andP[y1_eq_y2 y1_neq0].
        by congr (|_, _|); ssfield; rewrite ?neq0 //.
      * have H1 : x2 - x1 != 0 by rewrite subr_eq0 eq_sym.
        have H2 : x2 * 3%:R + M#a - (x1 * 3%:R + M#a) != 0.
          rewrite subr_eq0 (inj_eq (addIr _)) (inj_eq (mulIf _)) ?ecu_chi3 //.
          by rewrite eq_sym.
        by congr (|_, _|); ssfield; rewrite ?neq0 //.
  Qed.

  Lemma ec_of_mc_pointD' : forall p q, oncurve M p -> oncurve M q ->
    ec_of_mc_point (MCGroup.add_no_check M p q) = ECGroup.add E (ec_of_mc_point p) (ec_of_mc_point q).
  Proof.
    move => p q Hp Hq.
    rewrite MCGroup.add_no_check_eq //.
    by apply ec_of_mc_pointD.
  Qed.

  Lemma ec_of_mc_pointN : forall p,
    ec_of_mc_point (MCGroup.neg p) = ECGroup.neg (ec_of_mc_point p).
  Proof. by move=> [|x y] //=; rewrite mulNr. Qed.
End MCEC.

Section MCAssocFin.
  Variable K : finECUFieldType.
  Variable M : mcuType K.

(*   Local Notation "x \+ y" := (@MCGroup.add _ _ x y). *)

  Local Notation "x \+ y" := (@MCGroup.add_no_check _ _ x y).

  Lemma addmA_fin: associative (@MCGroup.addmc K M).
  Proof.
    move=> p q r /=.
    pose oncve_p := [oc of p].
    pose oncve_q := [oc of q].
    pose oncve_r := [oc of r].
    apply/eqP; rewrite !eqE /=; apply/eqP.
    rewrite -[p \+ _](ec_of_mc_pointK M) !ec_of_mc_pointD' //;
      last exact: MCGroup.addO'.
    move: (addeA_fin (ec_of_mc p) (ec_of_mc q) (ec_of_mc r)).
    move/eqP; rewrite !eqE /= => /eqP ->.
    rewrite -!ec_of_mc_pointD' // ?ec_of_mc_pointK //;
      last exact: MCGroup.addO'.
  Qed.

  Definition finmc_zmodMixin := 
    (ZmodMixin
       addmA_fin (MCGroup.addmC (M := M))
       (MCGroup.add0m (M := M)) (MCGroup.addNm (M := M))).

  Canonical Structure finmc_zmodType :=
    Eval hnf in (ZmodType (mc M) finmc_zmodMixin).

  Lemma ec_of_mc_additive : additive (@ec_of_mc _ M).
  Proof.
    move=> p q.
    pose oncve_p := [oc of p].
    pose oncve_q := [oc of q].
    apply/eqP; rewrite !eqE /=; apply/eqP.
    by rewrite ec_of_mc_pointD' -?MCGroup.oncurveN // ec_of_mc_pointN.
  Qed.
End MCAssocFin.
