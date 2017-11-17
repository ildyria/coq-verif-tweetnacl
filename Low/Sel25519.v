From Tweetnacl Require Import Libs.Export.

Open Scope Z.

(* Some definitions relating to the functional spec of this particular program.  *)
Definition list_cswap (b:Z) (p q : list Z) : list Z := 
  if (Z.eqb b 0) then
    p
  else q.

Lemma list_cswap_nth_true: forall i d p q,
  nth i (list_cswap 1 p q) d = nth i q d.
Proof. go. Qed.

Lemma list_cswap_nth_false: forall i d p q,
  nth i (list_cswap 0 p q) d = nth i p d.
Proof. go. Qed.

Lemma list_cswap_length_eq: forall b p q, length p = length q -> length p = length (list_cswap b p q).
Proof. intros; unfold list_cswap; destruct (Z.eqb b 0); go. Qed.

Lemma list_cswap_Zlength_eq: forall b p q, Zlength p = Zlength q -> Zlength p = Zlength (list_cswap b p q).
Proof. intros; unfold list_cswap; destruct (Z.eqb b 0); go. Qed.

Lemma list_cswap_bound_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin <= x <= pmax) p ->
  Forall (fun x => qmin <= x <= qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (list_cswap b p q).
Proof.
move=> p pmin pmax q qmin qmax Hp Hq.
elim => [|?|?]; unfold list_cswap ; simpl;
eapply list.Forall_impl ; eauto;
intros x H; simpl in H;
destruct H as [Hmin Hmax]; split;
eapply Z.le_trans ; eauto;
try apply Z.le_min_l;try apply Z.le_min_r;try apply Z.le_max_l;try apply Z.le_max_r.
Qed.

Lemma list_cswap_bound_lt_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (list_cswap b p q).
Proof.
move=> p pmin pmax q qmin qmax Hp Hq.
elim => [|?|?]; unfold list_cswap ; simpl;
eapply list.Forall_impl ; eauto;
intros x H; simpl in H;
destruct H as [Hmin Hmax]; split;apply Z.lt_le_incl;
try solve[
eapply Z.le_lt_trans ; eauto;
try apply Z.le_min_l;try apply Z.le_min_r;try apply Z.le_max_l;try apply Z.le_max_r];
eapply Z.lt_le_trans ; eauto;
try apply Z.le_min_l;try apply Z.le_min_r;try apply Z.le_max_l;try apply Z.le_max_r.
Qed.

Lemma list_cswap_bound_lt : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin < x < Z.max pmax qmax) (list_cswap b p q).
Proof.
move=> p pmin pmax q qmin qmax Hp Hq.
elim => [|?|?]; unfold list_cswap ; simpl;
eapply list.Forall_impl ; eauto;
intros x H; simpl in H;
destruct H as [Hmin Hmax]; split;
try solve[
eapply Z.le_lt_trans ; eauto;
try apply Z.le_min_l;try apply Z.le_min_r;try apply Z.le_max_l;try apply Z.le_max_r];
eapply Z.lt_le_trans ; eauto;
try apply Z.le_min_l;try apply Z.le_min_r;try apply Z.le_max_l;try apply Z.le_max_r.
Qed.

Close Scope Z.

Definition Sel25519 b p q := list_cswap b p q.

Lemma Sel25519_length_eq: forall b p q, length p = length q -> length p = length (Sel25519 b p q).
Proof. rewrite /Sel25519 ; apply list_cswap_length_eq. Qed.

Lemma Sel25519_Zlength_eq: forall b p q, Zlength p = Zlength q -> Zlength p = Zlength (Sel25519 b p q).
Proof. rewrite /Sel25519 ; apply list_cswap_Zlength_eq. Qed.

Lemma Sel25519_length: forall b p q,
  length p = 16 ->
  length q = 16 ->
  length (Sel25519 b p q) = 16.
Proof. intros; rewrite -Sel25519_length_eq; omega. Qed.


Open Scope Z.

Lemma Sel25519_Zlength: forall b p q,
  Zlength p = 16 ->
  Zlength q = 16 ->
  Zlength (Sel25519 b p q) = 16.
Proof. intros; rewrite -Sel25519_Zlength_eq; omega. Qed.

Lemma Sel25519_bound_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin <= x <= pmax) p ->
  Forall (fun x => qmin <= x <= qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (list_cswap b p q).
Proof. rewrite /Sel25519 ; apply list_cswap_bound_le. Qed.

Lemma Sel25519_bound_lt_le : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin <= x <= Z.max pmax qmax) (Sel25519 b p q).
Proof. rewrite /Sel25519 ; apply list_cswap_bound_lt_le. Qed.

Lemma Sel25519_bound_lt : forall p pmin pmax q qmin qmax,
  Forall (fun x => pmin < x < pmax) p ->
  Forall (fun x => qmin < x < qmax) q -> forall b,
  Forall (fun x => Z.min pmin qmin < x < Z.max pmax qmax) (Sel25519 b p q).
Proof. rewrite /Sel25519 ; apply list_cswap_bound_lt. Qed.

Close Scope Z.