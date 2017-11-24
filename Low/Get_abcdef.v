Require Import Tweetnacl.Libs.Export.

Definition get_a (t:(list Z * list Z * list Z * list Z * list Z * list Z)) : list Z := match t with
  (a,b,c,d,e,f) => a
end.
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

Lemma get_a_length : forall a b c d e f, length (get_a (a,b,c,d,e,f)) = length a. Proof. go. Qed.
Lemma get_b_length : forall a b c d e f, length (get_b (a,b,c,d,e,f)) = length b. Proof. go. Qed.
Lemma get_c_length : forall a b c d e f, length (get_c (a,b,c,d,e,f)) = length c. Proof. go. Qed.
Lemma get_d_length : forall a b c d e f, length (get_d (a,b,c,d,e,f)) = length d. Proof. go. Qed.
Lemma get_e_length : forall a b c d e f, length (get_e (a,b,c,d,e,f)) = length e. Proof. go. Qed.
Lemma get_f_length : forall a b c d e f, length (get_f (a,b,c,d,e,f)) = length f. Proof. go. Qed.

Open Scope Z.

Lemma get_a_Zlength : forall a b c d e f, Zlength (get_a (a,b,c,d,e,f)) = Zlength a. Proof. go. Qed.
Lemma get_b_Zlength : forall a b c d e f, Zlength (get_b (a,b,c,d,e,f)) = Zlength b. Proof. go. Qed.
Lemma get_c_Zlength : forall a b c d e f, Zlength (get_c (a,b,c,d,e,f)) = Zlength c. Proof. go. Qed.
Lemma get_d_Zlength : forall a b c d e f, Zlength (get_d (a,b,c,d,e,f)) = Zlength d. Proof. go. Qed.
Lemma get_e_Zlength : forall a b c d e f, Zlength (get_e (a,b,c,d,e,f)) = Zlength e. Proof. go. Qed.
Lemma get_f_Zlength : forall a b c d e f, Zlength (get_f (a,b,c,d,e,f)) = Zlength f. Proof. go. Qed.

Close Scope Z.