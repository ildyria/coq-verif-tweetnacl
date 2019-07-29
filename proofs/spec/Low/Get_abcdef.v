Require Import Tweetnacl.Libs.Export.
Require Export Tweetnacl.Gen.Get_abcdef.

(*
Definition get_b (t:(list Z * list Z * list Z * list Z * list Z * list Z)) : list Z := match t with
  (a,b,c,d,e,f) => b
end.
Definition get_c (t:(list Z * list Z * list Z * list Z * list Z * list Z)) : list Z := match t with
  (a,b,c,d,e,f) => c
end.
Definition get_d (t:(list Z * list Z * list Z * list Z * list Z * list Z)) : list Z := match t with
  (a,b,c,d,e,f) => d
end.
Definition get_e (t:(list Z * list Z * list Z * list Z * list Z * list Z)) : list Z := match t with
  (a,b,c,d,e,f) => e
end.
Definition get_f (t:(list Z * list Z * list Z * list Z * list Z * list Z)) : list Z := match t with
  (a,b,c,d,e,f) => f
end.
*)
Definition get_m (c:(list Z * list Z)) : list Z := match c with
  (m,t) => m
end.
Definition get_t (c:(list Z * list Z)) : list Z := match c with
  (m,t) => t
end.


Lemma get_a_length : forall (a b c d e f:list Z), length (get_a (a,b,c,d,e,f)) = length a. Proof. go. Qed.
Lemma get_b_length : forall (a b c d e f:list Z), length (get_b (a,b,c,d,e,f)) = length b. Proof. go. Qed.
Lemma get_c_length : forall (a b c d e f:list Z), length (get_c (a,b,c,d,e,f)) = length c. Proof. go. Qed.
Lemma get_d_length : forall (a b c d e f:list Z), length (get_d (a,b,c,d,e,f)) = length d. Proof. go. Qed.
Lemma get_e_length : forall (a b c d e f:list Z), length (get_e (a,b,c,d,e,f)) = length e. Proof. go. Qed.
Lemma get_f_length : forall (a b c d e f:list Z), length (get_f (a,b,c,d,e,f)) = length f. Proof. go. Qed.
Lemma get_m_length : forall m t, length (get_m (m,t)) = length m. Proof. go. Qed.
Lemma get_t_length : forall m t, length (get_t (m,t)) = length t. Proof. go. Qed.

Open Scope Z.

Lemma get_a_Zlength : forall (a b c d e f:list Z), Zlength (get_a (a,b,c,d,e,f)) = Zlength a. Proof. go. Qed.
Lemma get_b_Zlength : forall (a b c d e f:list Z), Zlength (get_b (a,b,c,d,e,f)) = Zlength b. Proof. go. Qed.
Lemma get_c_Zlength : forall (a b c d e f:list Z), Zlength (get_c (a,b,c,d,e,f)) = Zlength c. Proof. go. Qed.
Lemma get_d_Zlength : forall (a b c d e f:list Z), Zlength (get_d (a,b,c,d,e,f)) = Zlength d. Proof. go. Qed.
Lemma get_e_Zlength : forall (a b c d e f:list Z), Zlength (get_e (a,b,c,d,e,f)) = Zlength e. Proof. go. Qed.
Lemma get_f_Zlength : forall (a b c d e f:list Z), Zlength (get_f (a,b,c,d,e,f)) = Zlength f. Proof. go. Qed.
Lemma get_m_Zlength : forall m t, Zlength (get_m (m,t)) = Zlength m. Proof. go. Qed.
Lemma get_t_Zlength : forall m t, Zlength (get_t (m,t)) = Zlength t. Proof. go. Qed.

Close Scope Z.