Require Export Tools.
Require Export notations.

Open Scope Z.

(*Notation "A :𝓖𝓕" := (A mod (2^255 - 19)) (at level 80, right associativity).*)

Lemma t2256is38 : (2^256 :𝓖𝓕 ) = (38 :𝓖𝓕).
Proof.
compute.
reflexivity.
(*
change 38 with (2 * 19).
change 256 with (Z.succ 255).
rewrite Z.pow_succ_r ; try omega.
rewrite <- Zmult_mod_idemp_r.
symmetry.
rewrite <- Zmult_mod_idemp_r.
f_equal.
*)
Qed.

Definition reduce n := 
  let c := n / 2^(256) in
  n + 38 * c - 2^(256) * c.

Lemma reduceFF : forall m, (reduce m :𝓖𝓕) = (m :𝓖𝓕).
Proof.
intro m.
unfold reduce.
rewrite <- Zminus_mod_idemp_r.
rewrite <- Zminus_mod_idemp_l.
rewrite <- Zplus_mod_idemp_r.
rewrite <- Zmult_mod_idemp_l.
rewrite <- t2256is38.
rewrite <- Zplus_mod_idemp_l.
rewrite Zminus_mod_idemp_l.
rewrite Zmult_mod_idemp_l.
rewrite <- Z.add_sub_assoc.
rewrite <- Zminus_diag_reverse.
rewrite <- Zplus_0_r_reverse.
rewrite Zmod_mod.
reflexivity.
Qed.
(*
Definition reduce_light_top n := 
  let c := n / 2^(16) in
  n - 2^(16) * c.

Definition reduce_light_bot n := 
  let c := n / 2^(16) in
  38 * c.
*)