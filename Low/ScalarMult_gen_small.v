Require Import Tweetnacl.Libs.Export.

Section ScalarRec.

Variable A : list Z -> list Z -> list Z.
Variable M : list Z -> list Z -> list Z.
Variable Zub : list Z -> list Z -> list Z.
Variable Sq : list Z -> list Z.
Variable _121665: list Z.
Variable Sel25519 : Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Definition fa r (a b c d e f x:list Z) :=
  Sel25519 r
     (M (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (Sq
        (A
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))).

Definition fb r (a b c d e f x:list Z) :=
  Sel25519 r
     (Sq
        (A
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d)))))
     (M (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))).

Definition fc r (a b c d e f x:list Z) :=
Sel25519 r
  (M
     (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (A
        (M
           (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
              (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))) _121665)
        (Sq (A (Sel25519 r a b) (Sel25519 r c d)))))
  (M
     (Sq
        (Zub
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))) x).

Definition fd r (a b c d e f x:list Z) :=
Sel25519 r
  (M
     (Sq
        (Zub
           (M (A (Sel25519 r b a) (Sel25519 r d c))
              (Zub (Sel25519 r a b) (Sel25519 r c d)))
           (M (Zub (Sel25519 r b a) (Sel25519 r d c))
              (A (Sel25519 r a b) (Sel25519 r c d))))) x)
  (M
     (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
        (Sq (Zub (Sel25519 r a b) (Sel25519 r c d))))
     (A
        (M
           (Zub (Sq (A (Sel25519 r a b) (Sel25519 r c d)))
              (Sq (Zub (Sel25519 r a b) (Sel25519 r c d)))) _121665)
        (Sq (A (Sel25519 r a b) (Sel25519 r c d))))).

Definition fe r (a b c d e f x:list Z) :=
A
  (M (A (Sel25519 r b a) (Sel25519 r d c))
     (Zub (Sel25519 r a b) (Sel25519 r c d)))
  (M (Zub (Sel25519 r b a) (Sel25519 r d c))
     (A (Sel25519 r a b) (Sel25519 r c d))).

Definition ff r (a b c d e f x:list Z) :=
  Sq (Zub (Sel25519 r a b) (Sel25519 r c d)).

Close Scope Z.

(* Variable A_length : forall a b, length a = 16 -> length b = 16 -> length (A a b) = 16.
Variable M_length : forall a b, length a = 16 -> length b = 16 -> length (M a b) = 16.
Variable Zub_length : forall a b, length a = 16 -> length b = 16 -> length (Zub a b) = 16.
Variable Sq_length : forall a, length a = 16 -> length (Sq a) = 16.
Variable Sel25519_length : forall b p q, length p = 16 -> length q = 16 -> length (Sel25519 b p q) = 16.
Variable _121665_length : length _121665 = 16. *)

Open Scope Z.

Variable A_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (A a b) = 16.
Variable M_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (M a b) = 16.
Variable Zub_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (Zub a b) = 16.
Variable Sq_Zlength : forall a, Zlength a = 16 -> Zlength (Sq a) = 16.
Variable Sel25519_Zlength : forall b p q, Zlength p = 16 -> Zlength q = 16 -> Zlength (Sel25519 b p q) = 16.
Variable _121665_Zlength : Zlength _121665 = 16.

Close Scope Z.
(* 
Local Ltac solve_small_montgomery_step_gen_length :=
  intros;
  rewrite /fa /fb /fc /fd /fe /ff;
  repeat match goal with
    | _ => orewrite Sel25519_length
    | _ => orewrite M_length
    | _ => orewrite Sq_length
    | _ => orewrite A_length
    | _ => orewrite Zub_length
  end ; reflexivity.

Lemma fa_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fa r a b c d e f x) = 16.
Proof. solve_small_montgomery_step_gen_length. Qed.
Lemma fb_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fb r a b c d e f x) = 16.
Proof. solve_small_montgomery_step_gen_length. Qed.
Lemma fc_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fc r a b c d e f x) = 16.
Proof. solve_small_montgomery_step_gen_length. Qed.
Lemma fd_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fd r a b c d e f x) = 16.
Proof. solve_small_montgomery_step_gen_length. Qed.
Lemma fe_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (fe r a b c d e f x) = 16.
Proof. solve_small_montgomery_step_gen_length. Qed.
Lemma ff_length : forall r a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 -> length x = 16 ->
  length (ff r a b c d e f x) = 16.
Proof. solve_small_montgomery_step_gen_length. Qed. *)

Open Scope Z.

Local Ltac solve_small_step_Zlength :=
  intros;
  rewrite /fa /fb /fc /fd /fe /ff;
  repeat match goal with
    | _ => orewrite Sel25519_Zlength
    | _ => orewrite M_Zlength
    | _ => orewrite Sq_Zlength
    | _ => orewrite A_Zlength
    | _ => orewrite Zub_Zlength
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

Variable M_bound_Zlength : forall a b,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Variable Sq_bound_Zlength : forall a,
  Zlength a = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Sq a).
Variable A_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 + m2 <= x <= n1 + n2) (A a b).
Variable A_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 + m2 < x < n1 + n2) (A a b).
Variable Zub_bound_Zlength_le : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 <= x <= n1) a -> 
  Forall (fun x => m2 <= x <= n2) b -> 
  Forall (fun x => m1 - n2 <= x <= n1 - m2) (Zub a b).
Variable Zub_bound_Zlength_lt : forall m1 n1 m2 n2 a b,
  Zlength a = Zlength b ->
  Forall (fun x => m1 < x < n1) a -> 
  Forall (fun x => m2 < x < n2) b -> 
  Forall (fun x => m1 - n2 < x < n1 - m2) (Zub a b).
Variable Sel25519_bound_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin <= x <= pmax) p ->
  Forall (fun x => qmin <= x <= qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q).
(* Variable Sel25519_bound_lt_trans_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q).
 *)
(*
Variable Sel25519_bound_lt : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin < x < Z.max pmax qmax) (Sel25519 b p q).
*)
Variable Sel25519_bound_lt_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x < pmax) p ->
  Forall (fun x => pmin <= x < pmax) q -> forall b,
  Forall (fun x => pmin <= x < pmax) (Sel25519 b p q).
Variable Sel25519_bound_lt_lt_id : forall pmin pmax p q,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => pmin < x < pmax) q -> forall b,
  Forall (fun x => pmin < x < pmax) (Sel25519 b p q).
(*
Variable Sel25519_bound_le_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x <= pmax) p ->
  Forall (fun x => pmin <= x <= pmax) q -> forall b,
  Forall (fun x => pmin <= x <= pmax) (Sel25519 b p q). 
*)
Variable Sel25519_bound_le_lt_trans_le_id : forall pmin pmax p q,
  Forall (fun x => pmin <= x < pmax) p ->
  Forall (fun x => pmin <= x < pmax) q -> forall b,
  Forall (fun x => pmin <= x <= pmax) (Sel25519 b p q).
Variable _121665_bound : Forall (fun x => 0 <= x < 2 ^16) _121665.

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
  assumption.
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
  apply _121665_bound.
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
  apply _121665_Zlength.
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
  apply _121665_bound.
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