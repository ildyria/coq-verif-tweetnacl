(* r=(z[15]>>16)&1; *)

Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.ListsOp.Export.
Require Import ssreflect.
Require Import stdpp.prelude.

Open Scope Z.

Definition getbit_25519  (l : list Z) := Z.land ((Z.shiftr (nth (Z.to_nat 15) l 0)  16)) 1.

Lemma getbit_25519_0_or_1 : forall l,
  0 <= getbit_25519 l <= 1.
Proof.
intros.
unfold getbit_25519.
apply and_0_or_1.
Qed.

Lemma getbit_25519_repr : forall l,
  16 = Zlength l ->
  Forall (fun x => 0 <= x < 2^16) (firstn (Z.to_nat 15) l) ->
  -32768 <= nth (Z.to_nat 15) l 0 < 2^16->
  Z.land (Z.shiftr (ZofList 16 l) 256) 1 = getbit_25519 l.
Proof.
rewrite /getbit_25519.
move=> l Hl Hlb Hl15.
rewrite Zlength_correct in Hl.
change (Z.to_nat 15) with 15%nat in *.
rewrite (ZofList_nth_last_div 16) ; try omega; try assumption.
change (16 * 15%nat) with 240.
rewrite -Z.shiftr_div_pow2 ; try omega.
rewrite Z.shiftr_shiftr ; try omega.
reflexivity.
Qed.

Close Scope Z.