Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Gen.AMZubSqSel_List.
Require Import Tweetnacl.Gen.ABCDEF.
Require Import ssreflect.


(* This is so generic that it could possibly go to Gen folder *)

Section ScalarRec.
Open Scope Z.

Context {O : Ops (list Z) (list Z) id}.
Context {OP : @Ops_List O}.

Local Ltac solve_small_step_Zlength :=
  intros;
  rewrite /fa /fb /fc /fd /fe /ff;
  repeat match goal with
    | _ => orewrite Sel25519_Zlength
    | _ => orewrite M_Zlength
    | _ => orewrite Sq_Zlength
    | _ => orewrite A_Zlength
    | _ => orewrite Zub_Zlength
    | _ => apply C_121665_Zlength
    | _ => apply OP
  end ; reflexivity.

Lemma fa_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fa r a b c d e f x) = 16.
Proof. solve_small_step_Zlength. Qed.

Lemma fb_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fb r a b c d e f x) = 16.
Proof. solve_small_step_Zlength. Qed.

Lemma fc_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fc r a b c d e f x) = 16.
Proof. solve_small_step_Zlength. Qed.

Lemma fd_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fd r a b c d e f x) = 16.
Proof. solve_small_step_Zlength. Qed.

Lemma fe_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fe r a b c d e f x) = 16.
Proof. solve_small_step_Zlength. Qed.

Lemma ff_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (ff r a b c d e f x) = 16.
Proof. solve_small_step_Zlength. Qed.

Local Ltac Simplify_this :=
change (2^16) with 65536 in *;
change (2^26) with 67108864 in *.

Lemma fa_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fa r a b c d e f x).
Proof.
  intros ; simpl.
  apply Sel25519_bound_lt_le_id.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_le.
  solve_small_step_Zlength.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  eapply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

Lemma fb_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fb r a b c d e f x).
Proof.
  intros.
  simpl.
  apply Sel25519_bound_lt_le_id.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.


Lemma fc_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fc r a b c d e f x).
Proof.
  intros.
  simpl.
  apply Sel25519_bound_lt_le_id.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_le.
  solve_small_step_Zlength.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  eapply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply C_121665_bound.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  assumption.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl ; eauto.
  intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

Lemma fd_bound : forall r a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fd r a b c d e f x).
Proof.
  intros.
  simpl.
  apply Sel25519_bound_lt_le_id.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  assumption.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl ; eauto.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_small_step_Zlength.
  apply C_121665_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply C_121665_bound.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_small_step_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_small_step_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

End ScalarRec.

Close Scope Z.