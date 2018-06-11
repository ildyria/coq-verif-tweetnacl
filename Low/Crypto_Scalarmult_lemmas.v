From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.
From stdpp Require Import list.
Require Import ssreflect.

From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import AMZubSqSel_Prop.
From Tweetnacl.Gen Require Import AMZubSqSel_List.
From Tweetnacl.Gen Require Import Get_abcdef.
From Tweetnacl.Gen Require Import abstract_fn_rev.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Low Require Import List16.
From Tweetnacl.Gen Require Import abstract_fn_rev_eq.
From Tweetnacl.Gen Require Import abstract_fn_rev_abcdef.
From Tweetnacl.Low Require Import Constant.
From Tweetnacl.Low Require Import AMZubSqSel_Correct.
From Tweetnacl.Low Require Import Crypto_Scalarmult.
From Tweetnacl.Mid Require Import Crypto_Scalarmult.
From Tweetnacl.Low Require Import ScalarMult_rev.
From Tweetnacl.Low Require Import Crypto_Scalarmult_lemmas_Z_List16.
From Tweetnacl.Low Require Import Crypto_Scalarmult_lemmas_List_List16.
From Tweetnacl.Low Require Import Unpack25519.
From Tweetnacl.Low Require Import Pack25519.
From Tweetnacl.Low Require Import Inv25519.
From Tweetnacl.Low Require Import Prep_n.
From Tweetnacl.Low Require Import GetBit.
(* From Tweetnacl.Low Require Import M. *)
(* From Tweetnacl.Low Require Import A. *)
From Tweetnacl.Mid Require Import Unpack25519.
From Tweetnacl.Mid Require Import Pack25519.
From Tweetnacl.Mid Require Import Inv25519.
From Tweetnacl.Mid Require Import Prep_n.

Open Scope Z.

Section Crypto_Scalarmult_Eq_ac_List.

Context (Z_Ops                    : (Ops Z Z)).
Context (List_Z_Ops               : Ops (list Z) (list Z)).
Context (List_Z_Ops_Prop          : @Ops_List List_Z_Ops).
Context (List_Z_Ops_Prop_Correct  : @Ops_Prop_List_Z List_Z_Ops Z_Ops).
Local Instance List16_Ops         : (Ops (@List16 Z) (List32B)) := {}.
Proof.
apply A_List16.
apply M_List16.
apply Zub_List16.
apply Sq_List16.
apply C_0_List16.
apply C_1_List16.
apply C_121665_List16.
apply Sel25519_List16.
apply getbit_List32B.
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.
Local Instance List16_Z_Eq      : @Ops_Mod_P (@List16 Z) (List32B) Z List16_Ops Z_Ops := {
P l := (ZofList 16 (List16_to_List l));
P' l := (ZofList 8 (List32_to_List l));
}.
Proof.
- intros [a Ha] [b Hb] ; simpl ; f_equal; apply A_correct.
- intros [a Ha] [b Hb] ; simpl List16_to_List.
  apply mult_GF_Zlengh ; assumption.
- intros [a Ha] [b Hb] ; simpl ; f_equal ; apply Zub_correct.
- intros [a Ha] ; simpl List16_to_List ; apply Sq_GF_Zlengh ; assumption.
- simpl List16_to_List ; f_equal; apply C_121665_correct.
- simpl List16_to_List ; f_equal; apply C_0_correct.
- simpl List16_to_List ; f_equal; apply C_1_correct.
- intros b [p Hp] [q Hq] ; simpl List16_to_List ; f_equal ; apply Sel25519_correct.
- intros b [p Hp] ; simpl ; symmetry ; apply GetBit_correct ; assumption.
Defined.

(* Check @P (list Z) (list Z) Z.
Lemma abstract_fn_rev_eq_a_Z : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z) (n u:Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  ZofList 16 Up = u ->
  ZofList 8 Cn = n ->

  (@Mod Z Z Z_Ops) (P (Mod (get_a (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up)))) =
  (@Mod Z Z Z_Ops) (get_a (abstract_fn_rev m p n 1 u 0 1 0 0 u)).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up n u.
  intros Hm.
  intros HL16ONE HL16NUL HL16UP HL32CN.
  intros Hu Hn.
  assert(Heq1:= @abstract_fn_rev_eq_a (List16 Z) List32B Z List16_Ops Z_Ops List16_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /P /P' /List16_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN ?Hu ?Hn.
  change (ℤ16.lst nul16) with 0.
  change (ℤ16.lst One16) with 1.
  trivial.
Qed. *)

Theorem Crypto_Scalarmult_Eq : forall (n p:list Z),
  Zlength n = 32 ->
  Zlength p = 32 ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) n ->
  Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 8) p ->
  ZofList 8 (Crypto_Scalarmult n p) = ZCrypto_Scalarmult (ZofList 8 n) (ZofList 8 p).
Proof.
Admitted.
(* 
  intros n p Hln Hlp Hbn Hbp.
  rewrite /Crypto_Scalarmult ZCrypto_Scalarmult_eq /ZCrypto_Scalarmult_rev_gen /montgomery_fn.
  assert(HlOne16: Zlength One16 = 16) by go.
  assert(HlNul16: Zlength nul16 = 16) by go.
  assert(HbOne16: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) One16) by
    (repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go).
  assert(HbNul16: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) nul16) by
    (repeat rewrite Forall_cons ; jauto_set ; try apply Forall_nil ; compute ; go).
  assert(HUnpack: Forall (λ x : ℤ, 0 ≤ x ∧ x < 2 ^ 16) (Unpack25519 p)).
    apply Unpack25519_bounded.
    assumption.
  assert(HUnpackEx: Forall (λ x : ℤ, -38 ≤ x ∧ x < 2 ^ 16 + 38) (Unpack25519 p)).
    eapply list.Forall_impl.
    eassumption.
    apply impl_omega_simpl_0.
  assert(HlUnpackP: Zlength (Unpack25519 p) = 16).
    apply Unpack25519_Zlength.
    assumption.
   assert(HlgetA: Zlength (get_a (@abstract_fn_rev (list Z) (list Z) List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) =
16).
  {
  apply ScalarMult_rev_fn_gen.get_a_abstract_fn_Zlength ; try assumption.
  omega.
  }
  assert(HlgetC: Zlength (get_c (@abstract_fn_rev (list Z) (list Z) List_Z_Ops 255 254 (clamp n) One16 (Unpack25519 p) nul16 One16 nul16 nul16 (Unpack25519 p))) =
16).
  {
  apply ScalarMult_rev_fn_gen.get_c_abstract_fn_Zlength ; try assumption.
  omega.
  }
  rewrite Pack25519_mod_25519.
  2: {
  apply M.M_Zlength.
  2: apply Inv25519_Zlength.
  apply HlgetA.
  assumption.
  eapply ScalarMult_rev_fn_gen.get_c_abstract_fn_Zlength ; try assumption.
  omega.
  }
  2: {
  eapply list.Forall_impl.
  apply M.M_bound_Zlength.
  5: apply impl_omega_simpl_2.
  2: apply Inv25519_Zlength.
  1,2: assumption.
  eapply list.Forall_impl.
  apply get_a_montgomery_fn_bound.
  all: try assumption.
  omega.
  apply impl_omega_simpl_1.
  eapply list.Forall_impl.
  apply Inv25519_bound_Zlength.
  assumption.
  apply get_c_montgomery_fn_bound.
  all: try assumption.
  omega.
  apply impl_omega_simpl_1.
  }
  rewrite /ZPack25519.
  rewrite mult_GF_Zlengh.
  3: apply Inv25519_Zlength.
  2,3: assumption.
  rewrite -Zmult_mod_idemp_l.
  rewrite -Zmult_mod_idemp_r.
  symmetry.
  rewrite -Zmult_mod_idemp_l.
  rewrite -Zmult_mod_idemp_r.
  f_equal.
  f_equal.
  symmetry.
  2: rewrite Inv25519_Z_GF.
  3: assumption.
  2: rewrite Inv25519_Z_correct /ZInv25519.
  2: rewrite pow_mod.
  2: symmetry.
  2: rewrite pow_mod.
  3,4: compute; discriminate.
  2: f_equal ; f_equal.
  1,2: rewrite /Zmontgomery_fn /montgomery_fn.

  1,2: assert(H255: 0 <= 255) by omega.
  1: assert(Heq1:= @abstract_fn_rev_eq_a (List16 Z) List32B (list Z) List16_Ops List_Z_Ops List16_List_Z_Eq 255 254).
  1: assert(Heq2:= @abstract_fn_rev_eq_a (List16 Z) List32B Z List16_Ops Z_Ops List16_Z_Eq 255 254).
  2: assert(Heq1:= @abstract_fn_rev_eq_c (List16 Z) List32B (list Z) List16_Ops List_Z_Ops List16_List_Z_Eq 255 254).
  2: assert(Heq2:= @abstract_fn_rev_eq_c (List16 Z) List32B Z List16_Ops Z_Ops List16_Z_Eq 255 254).

  1,2: assert(HL32NForall:= clamp_bound n Hbn).
  1,2: pose(ExL32N := L32B (clamp n) HL32NForall).
  1,2: pose(L16ONE := Len One16 HlOne16).
  1,2: pose(L16NUL := Len nul16 HlNul16).
  1,2: pose(L16UP := Len (Unpack25519 p) HlUnpackP).

  1,2: assert(Heq1I := Heq1 ExL32N L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP H255).
  1,2: rewrite /Mod /List16_List_Z_Eq /List16_to_List /id in Heq1I.
  1,2: change (P L16NUL) with nul16 in Heq1I.
  1,2: change (P L16ONE) with One16 in Heq1I.
  1,2: change (P' ExL32N) with (clamp n) in Heq1I.
  1,2: change (P L16UP) with (Unpack25519 p) in Heq1I.
  1,2: rewrite -Heq1I.

  1,2: assert(Heq2I := Heq2 ExL32N L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP H255).
  1,2: change (P L16NUL) with 0 in Heq2I.
  1,2: change (P L16ONE) with 1 in Heq2I.

  1,2: assert(HL32N: P' ExL32N = Zclamp (ZofList 8 n)).
  1,3: simpl ; symmetry ; apply clamp_ZofList_eq; try assumption ; rewrite Zlength_correct in Hln ; omega.

  1,2: assert(HL16P: P L16UP = (ZUnpack25519 (ZofList 8 p))).
  1,3: simpl ; symmetry ; apply Unpack25519_eq_ZUnpack25519; try assumption ; rewrite Zlength_correct in Hlp ; omega.

  1,2: rewrite HL32N in Heq2I.
  1,2: rewrite HL16P in Heq2I.
  1,2: rewrite /Mod /List16_Z_Eq in Heq2I.
  1,2: rewrite /P.
  1,2: rewrite /P /List16_to_List in Heq2I.
  1,2: remember (Zclamp (ZofList 8 n)) as N.
  1,2: remember (ZUnpack25519 (ZofList 8 p)) as P.
  1,2: remember (2 ^ 255 - 19) as PRIME.
  1: remember ((ℤ16.lst match get_a (abstract_fn_rev 255 254 ExL32N L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP) with
                 | Len l _ => l
                 end) `mod` PRIME) as m.
  2: remember ((ℤ16.lst match get_c (abstract_fn_rev 255 254 ExL32N L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP) with
                 | Len l _ => l
                 end) `mod` PRIME) as m.
  1,2: clear Heqm.
  1,2: clears n p.
  1,2: clears Heq1 Heq2.
  1,2: clear L16ONE L16UP L16NUL ExL32N HL32N HL16P HeqPRIME HL32NForall.
  1,2: clears HlOne16 HlNul16 HbOne16 HbNul16 HlUnpackP H255.
  1,2: assumption.
Qed.
 *)

(* Lemma abstract_fn_rev_eq_a_Z : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z) (n u:Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  ZofList 16 Up = u ->
  ZofList 8 Cn = n ->
  Mod (P (get_a (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP))) =
  Mod (get_a (abstract_fn_rev m p n 1 u 0 1 0 0 u)).


Lemma abstract_fn_rev_eq_a : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  P (get_a (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP)) =
  get_a (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up.
  intros Hm.
  intros HL16ONE.
  intros HL16NUL.
  intros HL16UP.
  intros HL32CN.
  match goal with
    | [ |- ?A = ?B ] => change A with (id A) ; change B with (id B)
  end.
  assert(Heq1:= @abstract_fn_rev_eq_a (List16 Z) List32B (list Z) List16_Ops List_Z_Ops List16_List_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /Mod /P /P' /List16_List_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN.
  trivial.
Qed.

Lemma abstract_fn_rev_eq_c : ∀ (m p : ℤ) (CN : List32B) (L16ONE L16NUL L16UP : List16 ℤ) (Cn Up:list Z),
  0 ≤ m →
  List16_to_List L16ONE = One16 ->
  List16_to_List L16NUL = nul16 ->
  List16_to_List L16UP = Up ->
  List32_to_List CN = Cn ->
  P (get_c (abstract_fn_rev m p CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP)) =
  get_c (abstract_fn_rev m p Cn One16 Up nul16 One16 nul16 nul16 Up).
Proof.
  intros m p CN L16ONE L16NUL L16UP Cn Up.
  intros Hm.
  intros HL16ONE.
  intros HL16NUL.
  intros HL16UP.
  intros HL32CN.
  match goal with
    | [ |- ?A = ?B ] => change A with (id A) ; change B with (id B)
  end.
  assert(Heq1:= @abstract_fn_rev_eq_c (List16 Z) List32B (list Z) List16_Ops List_Z_Ops List16_List_Z_Eq m p).
  specialize Heq1 with CN L16ONE L16UP L16NUL L16ONE L16NUL L16NUL L16UP.
  apply Heq1 in Hm.
  clear Heq1.
  move:Hm.
  rewrite /Mod /P /P' /List16_List_Z_Eq ?HL16ONE ?HL16NUL ?HL16UP ?HL32CN.
  trivial.
Qed. *)

End Crypto_Scalarmult_Eq_ac_List.


