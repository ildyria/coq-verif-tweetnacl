From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import ListsOp.Export.
From Tweetnacl Require Import Low.Reduce_by_P_compose_step.

From stdpp Require Import prelude.
Require Import Recdef.

Open Scope Z.

Definition subst_0xffff t := t - 65535.

Definition sub_step_1 (a:Z) (m t:list Z) : list Z :=
    let t' := nth (Z.to_nat a) t 0 in
      (upd_nth (Z.to_nat a) m (subst_0xffff t')).



Close Scope Z.