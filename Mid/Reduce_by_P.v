From Tweetnacl Require Import Libs.Export.

Open Scope Z.


Definition red_by_P n :=
  let n' := n - (2^255-19) in
  if Z.leb 0 n' then
    let n'' := n' - (2^255-19) in 
    if Z.leb 0 n'' then
      n''
    else
      n'
  else
    n.

Lemma reduce_pos :  forall n, 0 <= n -> 0 <= red_by_P n.
Proof. move=> n Hn ; rewrite /red_by_P.
flatten.
apply Zle_bool_imp_le in Eq0.
omega.
apply Zle_bool_imp_le in Eq.
omega.
Qed.

Lemma reduce_max : forall n, n < 2^256 -> red_by_P n < 2 ^ 255 - 19.
Proof.
move => n Hn ; rewrite /red_by_P.
flatten.
{
apply Zle_bool_imp_le in Eq0.
apply Zle_bool_imp_le in Eq.
assert(n - (2 ^ 255 - 19) - (2 ^ 255 - 19) < 2 ^ 256 - (2 ^ 255 - 19) - (2 ^ 255 - 19)) by omega.
change (2 ^ 256 - (2 ^ 255 - 19) - (2 ^ 255 - 19)) with 38 in H.
change (2^255 - 19) with (57896044618658097711785492504343953926634992332820282019728792003956564819949) in *.
omega.
}
{
apply Zle_bool_imp_le in Eq.
apply Z.leb_gt in Eq0.
omega.
}
{
apply Z.leb_gt in Eq.
omega.
}
Qed.

Theorem reduce_P_mod_correct : forall n,
  (red_by_P n) mod (2^255-19) = n mod (2^255-19).
Proof.
  intros.
  rewrite /red_by_P.
  flatten;
  repeat match goal with 
    | _ => reflexivity
    | _ => rewrite -Zminus_0_l_reverse Z.mod_mod
    | _ => rewrite Zminus_mod ; change ((2 ^ 255 - 19) :𝓖𝓕) with 0
    | |- _ <> _ => compute ; go
  end.
Qed.

Theorem reduce_P_is_mod : forall n,
  0 <= n < 2 ^ 256 ->
  n mod (2^255-19) = red_by_P n.
Proof. intros.
rewrite -reduce_P_mod_correct.
apply Zmod_small.
split.
apply reduce_pos ; omega.
apply reduce_max ; omega.
Qed.

Close Scope Z.