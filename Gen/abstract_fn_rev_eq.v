From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Gen Require Import ABCDEF_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev.
Require Import ssreflect.

Open Scope Z.

Section Abstract_Fn_Rev_Eq_Thm.

Context {T : Type}.
Context {U : Type}.
Context {TO : Ops T}.
Context {UO : Ops U}.

Variable P : T -> U.
Variable Mod :U -> U.

Variable A_eq : forall a b, Mod (P (A a b)) = Mod (A (P a) (P b)).
Variable M_eq : forall a b, Mod (P (M a b)) = Mod (M (P a) (P b)).
Variable Zub_eq : forall a b,  Mod (P (Zub a b)) = Mod (Zub (P a) (P b)).
Variable Sq_eq : forall a,  Mod (P (Sq a)) = Mod (Sq (P a)).
Variable _121665_eq : Mod (P _121665) = Mod (_121665).
Variable Sel25519_eq : forall b p q,  Mod (P (Sel25519 b p q)) = Mod (Sel25519 b (P p) (P q)).
Variable getbit_eq : forall i p,  getbit i p = getbit i (P p).

Variable Mod_ZSel25519_eq : forall b p q,  Mod (Sel25519 b p q) = Sel25519 b (Mod p) (Mod q).
Variable Mod_ZA_eq : forall p q,  Mod (A p q) = Mod (A (Mod p) (Mod q)).
Variable Mod_ZM_eq : forall p q,  Mod (M p q) = Mod (M (Mod p) (Mod q)).
Variable Mod_ZZub_eq : forall p q,  Mod (Zub p q) = Mod (Zub (Mod p) (Mod q)).
Variable Mod_ZSq_eq : forall p,  Mod (Sq p) = Mod (Sq (Mod p)).
Variable Mod_red : forall p,  Mod (Mod p) = (Mod p).

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

End Abstract_Fn_Rev_Eq_Thm.

Close Scope Z.