Set Warnings "-notation-overridden,-parsing".

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div ssralg.
From Tweetnacl.High Require Import mc.
From Tweetnacl.High Require Import mcgroup.
From Tweetnacl.High Require Import ladder.
From Tweetnacl.High Require Import montgomery.

Import GRing.Theory.

Local Open Scope ring_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Section OptimizedLadder.
  Variable K : finECUFieldType.
  Variable M : mcuType K.

  Definition cswap {A : Type} (c : nat) (a b : A) :=
    if c == 1%N then (b, a) else (a, b).

  Fixpoint opt_montgomery_rec (n m : nat) (x a b c d : K) : K :=
    if m is m.+1 then
      let (a, b) := cswap (bitn n m) a b in
      let (c, d) := cswap (bitn n m) c d in
      let e := a + c in
      let a := a - c in
      let c := b + d in
      let b := b - d in
      let d := e^+2 in
      let f := a^+2 in
      let a := c * a in
      let c := b * e in
      let e := a + c in
      let a := a - c in
      let b := a^+2 in
      let c := d - f in
      let a := c * ((M#a - 2%:R) / 4%:R) in
      let a := a + d in
      let c := c * a in
      let a := d * f in
      let d := b * x in
      let b := e^+2 in
      let (a, b) := cswap (bitn n m) a b in
      let (c, d) := cswap (bitn n m) c d in
      opt_montgomery_rec n m x a b c d
    else
      a / c.

  Definition opt_montgomery (n m : nat) (x : K) : K :=
    opt_montgomery_rec n m x 1 x 0 1.

  Hypothesis mcu_no_square : forall x : K, x^+2 != (M#a)^+2 - 4%:R.

  Local Notation "p '#x0'" := (point_x0 p) (at level 30).
  Local Notation "p '#x'" := (point_x p) (at level 30).

  (* In montgomery.v we avoided relying on the fact that in ssreflect,
   * a / 0 = 0. However, the implementation in TweetNaCl considers the inverse
   * of 0 to be 0. Hence, we replicate this behaviour.
   *)
  Lemma point_x0_point_x_simple a b (p : point K) :
    inf_div a b = p#x -> a / b = p#x0.
  Proof.
    move=> H.
    case: (boolP (b == 0)) => [/eqP|] Hb.
    + rewrite {}Hb /= in H *.
      rewrite invr0 mulr0.
      case: p => [|p_x p_y] in H *; first by [].
      have : 0 != 0 :> K by apply: inf_div_K_Fin; exact: H.
      by rewrite eq_refl.
    + apply/eqP; rewrite eq_sym point_x0_point_x //; first by apply/eqP.
      case: p => [|p_x p_y] in H *; last by [].
      have : b == 0 by rewrite -(inf_div_K_Inf a); apply/eqP.
      by rewrite /= -(negbTE Hb).
  Qed.

  Local Notation "\- x"   := (@MCGroup.neg _ x).
  Local Notation "x \+ y" := (@MCGroup.add _ M x y).
  Local Notation "x \- y" := (x \+ (\- y)).

  Local Lemma opt_montgomery_rec_small (n m k : nat) (x a b c d : K) : k >= m ->
    opt_montgomery_rec (n + 2^k) m x a b c d = opt_montgomery_rec n m x a b c d.
  Proof.
    move=> Hm.
    elim: m => [|m IHm /=] in Hm a b c d *; first by [].
    rewrite bitn_large //.
    by case/orP: (bitnV n m) => /eqP-> /=; rewrite IHm 1?ltnW.
  Qed.

  Local Lemma opt_montgomery_rec_ok (n m : nat) (p q : mc M) (a b c d : K) :
    n < 2^m -> 
    p#x0 != 0 ->
    hom_ok a c -> hom_ok b d ->
    q#x = inf_div a c -> (p + q)#x = inf_div b d ->
    opt_montgomery_rec n m (p#x0) a b c d = (p *+ n + q *+ 2^m)#x0.
  Proof.
    move=> Hn Hp Hac_ok Hbd_ok /eqP Hac /eqP Hbd.
    move/andP: {Hac_ok Hac} (conj Hac_ok Hac) => Hac.
    move/andP: {Hbd_ok Hbd} (conj Hbd_ok Hbd) => Hbd.
    rewrite -montgomery_rec_ok //.
    elim: m => [|m IHm] in q a b c d n Hn Hac Hbd *.
      by rewrite /=; apply: point_x0_point_x_simple; move/andP: Hac => [_ /eqP].
    move/andP: Hac => [Hac_ok /eqP Hac].
    move/andP: Hbd => [Hbd_ok /eqP Hbd].
    have H1 : p#x = inf_div (p#x0) 1.
      rewrite /inf_div oner_eq0 divr1 point_x_K_Fin_point_x0 //.
      by apply: point_x0_neq0_fin.
    pose E := (oncurve_mc, oner_neq0, andbT).
    case: (boolP (n < 2^m)) => [{Hn} Hn|].
      rewrite /= bitn_small0 //= (IHm (q*+2)) //.
      + by rewrite [q + _]addrC -addrA -mulr2n.
      + rewrite [X in _ * (X + _)]mulrC [_ + (a + c)^+2]addrC mulr2n.
        apply/andP; split.
        - by apply: montgomery_hom_eq_ok.
        - by apply/eqP; apply: montgomery_hom_eq; rewrite ?E //.
      + rewrite -[_^+2]mul1r [_ * (a - c)]mulrC [_ * (a + c)]mulrC.
        rewrite [_ * p#x0]mulrC mulr2n addrCA.
        apply: montgomery_hom_neq; rewrite ?E //.
        by rewrite -[q \- _]/(point_of_mc (q-_)) addrC opprD addrNK point_x_neg.
    rewrite -leqNgt => Hngeq.
    rewrite -[n](@subnK (2^m)) //.
    have H3 : n - 2 ^ m < 2 ^ m.
      by rewrite -(@ltn_add2r (2^m)) subnK // addnn -mul2n -expnS.
    rewrite /= bitn_small1 //=.
    rewrite opt_montgomery_rec_small ?montgomery_rec_small ?leqnn //.
    rewrite [(p + q)*+2]mulr2n -addrA [q + (p + q)]addrC.
    rewrite (IHm (p + q + q)) //.
    + rewrite -[_^+2]mul1r [_ * (b - d)]mulrC [_ * (b + d)]mulrC.
      rewrite [_ * p#x0]mulrC.
      apply: montgomery_hom_neq; rewrite ?E //.
      by rewrite -[_ \- q]/(point_of_mc (_-q)) addrK.
    + rewrite [X in _*(X + _)]mulrC [_ + (b+d)^+2]addrC [p+q]addrC -addrA addrA.
      apply/andP; split.
      - by apply: montgomery_hom_eq_ok.
      - by apply/eqP; apply: montgomery_hom_eq; rewrite ?E //.
  Qed.

  Lemma opt_montgomery_ok (n m : nat) (x : K) :
    n < 2^m -> x != 0 ->
    forall (p : mc M), p#x0 = x -> opt_montgomery n m x = (p *+ n)#x0.
  Proof.
    move=> Hn x_neq0 p p_x_eqx.
    rewrite /opt_montgomery -{1}p_x_eqx -[p*+n]addr0 -[in _+0](@mul0rn _ (2^m)).
    apply: opt_montgomery_rec_ok; first by [].
    + by rewrite p_x_eqx.
    + by rewrite /hom_ok oner_eq0.
    + by rewrite /hom_ok oner_eq0 orbT.
    + by apply/eqP; rewrite eq_sym inf_div_K_Inf eq_refl.
    + apply/eqP; rewrite addr0 -point_x0_point_x.
      - by apply/eqP; rewrite divr1.
      - by exact: oner_neq0.
      - by apply: point_x0_neq0_fin; rewrite p_x_eqx.
  Qed.

  Lemma neg_x : forall (p : mc M),
    p#x0 = (-p)#x0.
  Proof.
    move=> [[|xp yp] Hp] //=.
  Qed.

  Lemma neg_x_n : forall (n:nat) (p : mc M),
    (p *+ n)#x0 = ((-p) *+ n)#x0.
  Proof.
    move => n p.
    rewrite GRing.mulNrn.
    apply neg_x.
  Qed.

Local Ltac ring_simplify_this :=
  repeat match goal with
  | _ => rewrite expr2
  | _ => rewrite exprS
  | _ => rewrite GRing.mul1r
  | _ => rewrite GRing.mulr1
  | _ => rewrite GRing.mul0r
  | _ => rewrite GRing.mulr0
  | _ => rewrite GRing.add0r
  | _ => rewrite GRing.oppr0
  | _ => rewrite GRing.addr0
  | _ => done
end.


Lemma opt_montgomery_rec_0 : forall (m n: nat) a b d,
  opt_montgomery_rec n m 0 a b 0 d = 0.
Proof.
  elim => [| m IHm] n a b d /=.
  + rewrite GRing.invr0 mulr0 //.
  + have/orP := bitnV n m.
    move => []/eqP => ->.
    all: rewrite /cswap => /=.
    all: ring_simplify_this.
    all: rewrite addrN.
    all: ring_simplify_this.
Qed.

Theorem opt_montgomery_0 (n m: nat):
  opt_montgomery n m 0 = 0.
Proof.
  rewrite /opt_montgomery.
  apply opt_montgomery_rec_0.
Qed.

End OptimizedLadder.
