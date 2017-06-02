From mathcomp Require Import ssreflect ssrbool eqtype ssrnat div ssralg.

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.

Section Ladders.
  Variable V : zmodType.

  Definition bitn (n k : nat) :=
    (n %/ (2^k)) %% 2.

  Lemma bit0n k : bitn 0 k = 0.
  Proof. by rewrite /bitn div0n. Qed.

  Lemma bitn_small0 n k : n < 2^k -> bitn n k = 0.
  Proof. by move=> H; rewrite /bitn divn_small. Qed.

  Lemma bitn_small1 n k : n < 2^k -> bitn (n + 2^k) k = 1.
  Proof.
    move=> H.
    rewrite /bitn divnDr; last by apply: dvdnn.
    by rewrite -modnDml -/(bitn n k) bitn_small0 // add0n divnn expn_gt0 /=.
  Qed.

  Lemma bitn_large n k l : l > k -> bitn (n + 2^l) k = bitn n k.
  Proof.
    move=> H1.
    have H2 : k <= l by apply: ltnW.
    rewrite /bitn divnDr; last by apply: dvdn_exp2l.
    rewrite -expnB // -modnDmr -modnXm modnn exp0n; last by rewrite subn_gt0.
    by rewrite mod0n addn0.
  Qed.

  Lemma bitnV n k : (bitn n k == 0) || (bitn n k == 1).
  Proof. by rewrite /bitn modn2; set b := odd _; case: b. Qed.

  Fixpoint doubleadd_rec (x : V) (n m : nat) (y : V) : V :=
    if m is m'.+1 then
      let y' := (y *+ 2)%R in
      let y'' := if bitn n m' == 1 then (y' + x)%R else y' in
      doubleadd_rec x n m' y''
    else y.

  Definition doubleadd (x : V) (n m : nat) : V :=
    doubleadd_rec x n m 0.

  Lemma doubleadd_recr0nr (x y : V) (m : nat) :
    doubleadd_rec x 0 m y = (y *+ 2^m)%R.
  Proof.
    elim: m y; first by [].
    by move=> m IHm y; rewrite /= bit0n /= IHm -mulrnA -expnS.
  Qed.

  Lemma doubleadd_rec_small (x y : V) (n m k : nat) :
    k >= m -> doubleadd_rec x (n + 2^k) m y = doubleadd_rec x n m y.
  Proof.
    elim: m y => [|m IHm y H /=]; first by [].
    by rewrite bitn_large // IHm; last by apply: ltnW.
  Qed.

  Lemma doubleadd_rec_ok (x y : V) (n m : nat) :
    n < 2^m -> doubleadd_rec x n m y = (x *+ n + y *+ 2^m)%R.
  Proof.
    elim: m => [|m IHm] in y n *.
      case: n => [|n].
        + by rewrite doubleadd_recr0nr mulr0n add0r.
        + by rewrite expn0 ltnS ltn0.
    case: (boolP (n < 2^m)) => [H _ /=|].
      by rewrite bitn_small0 //= IHm // -mulrnA -expnS.
    rewrite -leqNgt => Hngeq Hnlt.
    rewrite -[n](@subnK (2^m)) //.
    have H1 : n - 2 ^ m < 2 ^ m.
      by rewrite -(@ltn_add2r (2^m)) subnK // addnn -mul2n -expnS.
    rewrite /= bitn_small1 //= doubleadd_rec_small //.
    case: (boolP (n - 2^m == 0)) => [/eqP->|].
      by rewrite doubleadd_recr0nr add0n mulrnDl -mulrnA -expnS addrC.
    rewrite -lt0n => H2; rewrite -{1}[n - 2^m]prednK //.
    rewrite IHm prednK // subnK // mulrnBr // mulrnDl -mulrnA -expnS addrA.
    by rewrite -[(_ + y *+ _)%R]addrA [(_ + y *+ _)%R]addrC -!addrA addNr addr0.
  Qed.

  Lemma doubleadd_ok (x : V) (n m : nat) :
    n < 2^m -> doubleadd x n m = (x *+ n)%R.
  Proof. by move=> H; rewrite /doubleadd doubleadd_rec_ok // mul0rn addr0. Qed.

  Fixpoint montgomery_rec (n m : nat) (y z : V) : V :=
    if m is m'.+1 then
      if bitn n m' == 0 then
        let z' := (y + z)%R in
        let y' := (y*+2)%R in
        montgomery_rec n m' y' z'
      else
        let y' := (y + z)%R in
        let z' := (z*+2)%R in
        montgomery_rec n m' y' z'
    else y.

  Definition montgomery (x : V) (n m : nat) : V :=
    montgomery_rec n m 0 x.

  Lemma montgomery_rec_small (y z : V) (n m k : nat) :
    k >= m -> montgomery_rec (n + 2^k) m y z = montgomery_rec n m y z.
  Proof.
    elim: m y z => [|m IHm y z H /=]; first by [].
    by rewrite bitn_large // !IHm 1?ltnW.
  Qed.

  Lemma montgomery_rec_ok (x y : V) (n m : nat) :
    n < 2^m -> montgomery_rec n m y (x + y) = (x *+ n + y *+ 2^m)%R.
  Proof.
    move=> H.
    rewrite -doubleadd_rec_ok //.
    elim: m n y H => [|m IHm n y] /=; first by [].
    case: (boolP (n < 2^m)) => [H _|].
      rewrite [(y + _)%R]addrC -[(_ + y)%R]addrA -mulr2n mulrnDl.
      rewrite [(x*+2)%R]mulr2n -[(x + x + _)%R]addrA {2 3}[(x + _)%R]addrC.
      by rewrite !IHm //; case/orP: (bitnV n m) => /eqP->.
    rewrite -leqNgt => Hngeq Hnlt.
    rewrite -[n](@subnK (2^m)) //.
    have H1 : n - 2 ^ m < 2 ^ m.
      by rewrite -(@ltn_add2r (2^m)) subnK // addnn -mul2n -expnS.
    rewrite bitn_small1 //= montgomery_rec_small ?doubleadd_rec_small ?leqnn //.
    rewrite mulrnDl [(x*+2)%R]mulr2n -addrA [(x + y*+2)%R]addrC.
    by rewrite [(x + y)%R]addrC addrA -mulr2n IHm //.
  Qed.

  Lemma montgomery_ok (x : V) (n m : nat) :
    n < 2^m -> montgomery x n m = (x *+ n)%R.
  Proof.
    move=> H.
    by rewrite /montgomery -{1}[x]addr0 montgomery_rec_ok // mul0rn addr0.
  Qed.
End Ladders.
