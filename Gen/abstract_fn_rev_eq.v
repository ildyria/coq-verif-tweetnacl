From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import ABCDEF_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import Get_abcdef.
Require Import ssreflect.

Open Scope Z.

Section Abstract_Fn_Rev_Eq_Thm.

Context {T : Type}.
Context {U : Type}.
Context {TO : Ops T}.
Context {UO : Ops U}.
Context {UTO : @Ops_Mod_P T U TO UO}.

Theorem abstract_fn_rev_eq : forall (m p:Z) (z a b c d e f x a' b' c' d' e' f':T) (a'' b'' c'' d'' e'' f'': U),
  0 <= m ->
  (a',b',c',d',e',f') = (abstract_fn_rev m p z a b c d e f x) -> 
  (a'',b'',c'',d'',e'',f'') = (abstract_fn_rev m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x))
 ->
  Mod (P a') = Mod a'' /\
  Mod (P b') = Mod b'' /\
  Mod (P c') = Mod c'' /\
  Mod (P d') = Mod d'' /\
  Mod (P e') = Mod e'' /\
  Mod (P f') = Mod f''.
Proof.
  intros m p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f'' Hm.
  gen a'' b'' c'' d'' e'' f''.
  gen a' b' c' d' e' f'.
  gen p z a b c d e f x.
  pattern m.
  eapply natlike_ind.
  3: omega.
  move=> p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f''.
  rewrite abstract_fn_rev_equation Zle_imp_le_bool.
  rewrite abstract_fn_rev_equation Zle_imp_le_bool.
  2,3: omega. go.
  clear m Hm.
  intros m Hm IHm.
  intros p z a b c d e f x a' b' c' d' e' f' a'' b'' c'' d'' e'' f''.
  change (Z.succ m) with (m + 1).
  intros H' H''.
  rewrite abstract_fn_rev_equation in H'.
  rewrite abstract_fn_rev_equation in H''.
  replace (m + 1 - 1) with m in H' by omega.
  replace (m + 1 - 1) with m in H'' by omega.
  remember (abstract_fn_rev m p z a b c d e f x) as k'.
  remember (abstract_fn_rev m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x)) as k''.
  destruct k' as (((((a0',b0'),c0'),d0'),e0'),f0').
  destruct k'' as (((((a0'',b0''),c0''),d0''),e0''),f0'').
  replace (m + 1 <=? 0) with false in H'.
  replace (m + 1 <=? 0) with false in H''.
  2,3: symmetry ; apply Z.leb_gt ; omega.
  inversion H'.
  inversion H''.
  assert(Ht:= IHm p z a b c d e f x a0' b0' c0' d0' e0' f0' a0'' b0'' c0'' d0'' e0'' f0'' Heqk' Heqk'').
  jauto_set.
  all: rewrite -?fa_eq -?fb_eq -?fc_eq -?fd_eq -?fe_eq -?ff_eq ?getbit_eq.
  all: try assumption.
  1: rewrite fa_eq_mod ; try assumption ; symmetry ; rewrite fa_eq_mod ; try assumption.
  2: rewrite fb_eq_mod ; try assumption ; symmetry ; rewrite fb_eq_mod ; try assumption.
  3: rewrite fc_eq_mod ; try assumption ; symmetry ; rewrite fc_eq_mod ; try assumption.
  4: rewrite fd_eq_mod ; try assumption ; symmetry ; rewrite fd_eq_mod ; try assumption.
  5: rewrite fe_eq_mod ; try assumption ; symmetry ; rewrite fe_eq_mod ; try assumption.
  6: rewrite ff_eq_mod ; try assumption ; symmetry ; rewrite ff_eq_mod ; try assumption.
  all: symmetry ; f_equal ; f_equal ; assumption.
Qed.

Corollary abstract_fn_rev_eq_a : forall (m p:Z) (z a b c d e f x: T),
  0 <= m ->
  Mod (P (get_a (abstract_fn_rev m p z a b c d e f x))) = Mod (get_a (abstract_fn_rev m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x))).
Proof.
  intros.
  assert(H': exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev m p z a b c d e f x)).
  {
  rewrite abstract_fn_rev_equation.
  remember (abstract_fn_rev (m - 1) p z a b c d e f x) as k.
  destruct k as (((((a0',b0'),c0'),d0'),e0'),f0').
  flatten; do 6 eexists ; reflexivity.
  }
  assert(H'': exists a'' b'' c'' d'' e'' f'', (a'',b'',c'',d'',e'',f'') = (abstract_fn_rev m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x))).
  {
  rewrite abstract_fn_rev_equation.
  remember (abstract_fn_rev (m - 1) p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x)) as k.
  destruct k as (((((a0',b0'),c0'),d0'),e0'),f0').
  flatten; do 6 eexists ; reflexivity.
  }
  destruct H' as [a' [b' [c' [d' [e' [f' H']]]]]].
  destruct H'' as [a'' [b'' [c'' [d'' [e'' [f'' H'']]]]]].
  assert(H''':= abstract_fn_rev_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H' H'').
  destruct H''' as [Ha [_ [Hc _]]].
  apply (f_equal get_a) in H'.
  apply (f_equal get_a) in H''.
  simpl in H'.
  simpl in H''.
  subst.
  assumption.
Qed.

Corollary abstract_fn_rev_eq_c : forall (m p:Z) (z a b c d e f x: T),
  0 <= m ->
  Mod (P (get_c (abstract_fn_rev m p z a b c d e f x))) = Mod (get_c (abstract_fn_rev m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x))).
Proof.
  intros.
  assert(H': exists a' b' c' d' e' f', (a',b',c',d',e',f') = (abstract_fn_rev m p z a b c d e f x)).
  {
  rewrite abstract_fn_rev_equation.
  remember (abstract_fn_rev (m - 1) p z a b c d e f x) as k.
  destruct k as (((((a0',b0'),c0'),d0'),e0'),f0').
  flatten; do 6 eexists ; reflexivity.
  }
  assert(H'': exists a'' b'' c'' d'' e'' f'', (a'',b'',c'',d'',e'',f'') = (abstract_fn_rev m p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x))).
  {
  rewrite abstract_fn_rev_equation.
  remember (abstract_fn_rev (m - 1) p (P z) (P a) (P b) (P c) (P d) (P e) (P f) (P x)) as k.
  destruct k as (((((a0',b0'),c0'),d0'),e0'),f0').
  flatten; do 6 eexists ; reflexivity.
  }
  destruct H' as [a' [b' [c' [d' [e' [f' H']]]]]].
  destruct H'' as [a'' [b'' [c'' [d'' [e'' [f'' H'']]]]]].
  assert(H''':= abstract_fn_rev_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H' H'').
  destruct H''' as [Ha [_ [Hc _]]].
  apply (f_equal get_c) in H'.
  apply (f_equal get_c) in H''.
  simpl in H'.
  simpl in H''.
  subst.
  assumption.
Qed.

End Abstract_Fn_Rev_Eq_Thm.

Close Scope Z.