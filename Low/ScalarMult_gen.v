(* Require Import Tweetnacl.Libs.Export.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Gen.AMZubSqSel.
Require Import Tweetnacl.Low.AMZubSqSel.
Require Import ssreflect.

Section ScalarRec.

Context {O: Ops (list Z)}.
Context {OL: @Ops_Prop O}.

Open Scope Z.

Fixpoint montgomery_rec_gen (m : nat) (z a b c d e f x : list Z) : (list Z * list Z * list Z * list Z * list Z * list Z) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat n) z in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      let e := A a c in
      let a := Zub a c in
      let c := A b d in
      let b := Zub b d in
      let d := Sq e in
      let f := Sq a in
      let a := M c a in
      let c := M b e in
      let e := A a c in
      let a := Zub a c in
      let b := Sq a in
      let c := Zub d f in
      let a := M c _121665 in
      let a := A a d in
      let c := M c a in
      let a := M d f in
      let d := M b x in
      let b := Sq e in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      montgomery_rec_gen n z a b c d e f x
    end.

Definition montgomery_step_gen (m:nat) (z a b c d e f x : list Z) : (list Z * list Z * list Z * list Z * list Z * list Z)  :=
      let r := getbit (Z.of_nat m) z in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      let e := A a c in
      let a := Zub a c in
      let c := A b d in
      let b := Zub b d in
      let d := Sq e in
      let f := Sq a in
      let a := M c a in
      let c := M b e in
      let e := A a c in
      let a := Zub a c in
      let b := Sq a in
      let c := Zub d f in
      let a := M c _121665 in
      let a := A a d in
      let c := M c a in
      let a := M d f in
      let d := M b x in
      let b := Sq e in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      (a,b,c,d,e,f).
(*     end. *)

Lemma opt_montgomery_rec_step_gen : forall n z a b c d e f x,
  montgomery_rec_gen (S n) z a b c d e f x = 
  montgomery_rec_gen n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof. reflexivity. Qed.

Lemma opt_montgomery_rec_step_gen_ext : forall n z a b c d e f e' f' x,
  montgomery_rec_gen (S n) z a b c d e' f' x = 
  montgomery_rec_gen n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof. reflexivity. Qed.

(* Close Scope Z.

Local Ltac solve_montgomery_step_gen_length :=
  intros;
  rewrite /montgomery_step_gen;
  rewrite /get_a /get_b /get_c /get_d /get_e /get_f;
  rewrite /fa /fb /fc /fd /fe /ff;
  repeat match goal with
    | _ => orewrite Sel25519_length
    | _ => orewrite M_length
    | _ => orewrite Sq_length
    | _ => orewrite A_length
    | _ => orewrite Zub_length
    | _ => apply _121665_length
  end ; reflexivity.

Lemma get_a_montgomery_step_gen_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_a (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_length. Qed.
Lemma get_b_montgomery_step_gen_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_b (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_length. Qed.
Lemma get_c_montgomery_step_gen_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_c (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_length. Qed.
Lemma get_d_montgomery_step_gen_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_d (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_length. Qed.
Lemma get_e_montgomery_step_gen_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_e (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_length. Qed.
Lemma get_f_montgomery_step_gen_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_f (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_length. Qed.

Lemma get_a_montgomery_rec_gen_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_a (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_length. Qed.
Lemma get_b_montgomery_rec_gen_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_b (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_length. Qed.
Lemma get_c_montgomery_rec_gen_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_c (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_length. Qed.
Lemma get_d_montgomery_rec_gen_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_d (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_length. Qed.
Lemma get_e_montgomery_rec_gen_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_e (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_length. Qed.
Lemma get_f_montgomery_rec_gen_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (get_f (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_length. Qed.

Open Scope Z. *)

Local Ltac solve_montgomery_step_gen_Zlength :=
  intros;
  rewrite /montgomery_step_gen;
  rewrite /get_a /get_b /get_c /get_d /get_e /get_f;
  repeat match goal with
    | _ => orewrite Sel25519_Zlength
    | _ => orewrite M_Zlength
    | _ => orewrite Sq_Zlength
    | _ => orewrite A_Zlength
    | _ => orewrite Zub_Zlength
    | _ => apply _121665_Zlength
    | _ => apply OL
  end.

Lemma get_a_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength x = 16 ->
  Zlength (get_a (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_b_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength x = 16 ->
  Zlength (get_b (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_c_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength x = 16 ->
  Zlength (get_c (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_d_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength x = 16 ->
  Zlength (get_d (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_e_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength x = 16 ->
  Zlength (get_e (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_f_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength x = 16 ->
  Zlength (get_f (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.

Lemma get_a_montgomery_rec_gen_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_a (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_Zlength. Qed.
Lemma get_b_montgomery_rec_gen_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_b (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_Zlength. Qed.
Lemma get_c_montgomery_rec_gen_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_c (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_Zlength. Qed.
Lemma get_d_montgomery_rec_gen_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_d (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_Zlength. Qed.
Lemma get_e_montgomery_rec_gen_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_e (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_Zlength. Qed.
Lemma get_f_montgomery_rec_gen_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_f (montgomery_rec_gen n z a b c d e f x)) = 16.
Proof. induction n; intros ; [assumption|] ; simpl.
apply IHn ; try assumption ; solve_montgomery_step_gen_Zlength. Qed.

Local Ltac Simplify_this :=
change (2^16) with 65536 in *;
change (2^26) with 67108864 in *.

Lemma get_a_montgomery_step_bound : forall n z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (montgomery_step_gen  n z a b c d e f x)).
Proof.
  intros ; simpl.
  apply Sel25519_bound_lt_le_id.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_le.
  solve_montgomery_step_gen_Zlength.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
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

Lemma get_b_montgomery_step_bound : forall n z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (montgomery_step_gen  n z a b c d e f x)).
Proof.
  intros.
  simpl.
  apply Sel25519_bound_lt_le_id.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply A_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

Lemma get_c_montgomery_step_bound : forall n z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (montgomery_step_gen  n z a b c d e f x)).
Proof.
  intros.
  simpl.
  apply Sel25519_bound_lt_le_id.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply A_bound_Zlength_le.
  solve_montgomery_step_gen_Zlength.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  apply Sel25519_bound_le_lt_trans_le_id ; eauto.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Zub_bound_Zlength_lt.
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  apply _121665_bound.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  assumption.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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

Lemma get_d_montgomery_step_bound : forall n z a b c d e f x,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => -38 <= x < 2^16 + 38) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (montgomery_step_gen  n z a b c d e f x)).
Proof.
  intros.
  simpl.
  apply Sel25519_bound_lt_le_id.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  assumption.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; simpl in Hh; Simplify_this; omega.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  apply (Sel25519_bound_lt_lt_id (-39) (2 ^ 16 + 38)).
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  eapply list.Forall_impl ; eauto ; simpl ; intros ; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply M_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  apply _121665_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (Zub_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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
  apply _121665_bound.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  intros h Hh; Simplify_this; simpl in Hh; omega.
  eapply list.Forall_impl.
  apply Sq_bound_Zlength.
  solve_montgomery_step_gen_Zlength.
  eapply list.Forall_impl.
  apply (A_bound_Zlength_lt (-39) (2^16+ 38) (-39) (2^16+ 38)).
  solve_montgomery_step_gen_Zlength.
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

Lemma get_a_montgomery_rec_gen_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (montgomery_rec_gen  n z a b c d e f x)).
Proof.
induction n ; intros.
simpl ; auto.
rewrite opt_montgomery_rec_step_gen.
apply IHn ; try assumption.
apply get_a_montgomery_step_gen_Zlength ; auto.
apply get_b_montgomery_step_gen_Zlength ; auto.
apply get_c_montgomery_step_gen_Zlength ; auto.
apply get_d_montgomery_step_gen_Zlength ; auto.
apply get_a_montgomery_step_bound ; auto.
apply get_b_montgomery_step_bound ; auto.
apply get_c_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
apply get_d_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

Lemma get_b_montgomery_rec_gen_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (montgomery_rec_gen  n z a b c d e f x)).
Proof.
induction n ; intros.
simpl ; auto.
rewrite opt_montgomery_rec_step_gen.
apply IHn ; try assumption.
apply get_a_montgomery_step_gen_Zlength ; auto.
apply get_b_montgomery_step_gen_Zlength ; auto.
apply get_c_montgomery_step_gen_Zlength ; auto.
apply get_d_montgomery_step_gen_Zlength ; auto.
apply get_a_montgomery_step_bound ; auto.
apply get_b_montgomery_step_bound ; auto.
apply get_c_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
apply get_d_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

Lemma get_c_montgomery_rec_gen_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (montgomery_rec_gen  n z a b c d e f x)).
Proof.
induction n ; intros.
simpl ; auto.
rewrite opt_montgomery_rec_step_gen.
apply IHn ; try assumption.
apply get_a_montgomery_step_gen_Zlength ; auto.
apply get_b_montgomery_step_gen_Zlength ; auto.
apply get_c_montgomery_step_gen_Zlength ; auto.
apply get_d_montgomery_step_gen_Zlength ; auto.
apply get_a_montgomery_step_bound ; auto.
apply get_b_montgomery_step_bound ; auto.
apply get_c_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
apply get_d_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.
Lemma get_d_montgomery_rec_gen_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (montgomery_rec_gen  n z a b c d e f x)).
Proof.
induction n ; intros.
simpl ; auto.
rewrite opt_montgomery_rec_step_gen.
apply IHn ; try assumption.
apply get_a_montgomery_step_gen_Zlength ; auto.
apply get_b_montgomery_step_gen_Zlength ; auto.
apply get_c_montgomery_step_gen_Zlength ; auto.
apply get_d_montgomery_step_gen_Zlength ; auto.
apply get_a_montgomery_step_bound ; auto.
apply get_b_montgomery_step_bound ; auto.
apply get_c_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
apply get_d_montgomery_step_bound ; auto.
eapply list.Forall_impl ; eauto.
intros h Hh; Simplify_this; simpl in Hh; omega.
Qed.

Close Scope Z.
End ScalarRec. *)