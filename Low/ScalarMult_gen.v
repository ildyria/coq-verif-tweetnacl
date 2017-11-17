(*
int crypto_scalarmult(u8 *q,const u8 *n,const u8 *p)
{
  u8 z[32];
  i64 x[80],r;
  int i;
  gf a,b,c,d,e,f;
  FOR(i,31) z[i]=n[i];
  z[31]=(n[31]&127)|64;
  z[0]&=248;
  unpack25519(x,p);
  FOR(i,16) {
    b[i]=x[i];
    d[i]=a[i]=c[i]=0;
  }
  a[0]=d[0]=1;
  for(i=254;i>=0;--i) {
    r=(z[i>>3]>>(i&7))&1;
    sel25519(a,b,r);
    sel25519(c,d,r);
    A(e,a,c);
    Z(a,a,c);
    A(c,b,d);
    Z(b,b,d);
    S(d,e);
    S(f,a);
    M(a,c,a);
    M(c,b,e);
    A(e,a,c);
    Z(a,a,c);
    S(b,a);
    Z(c,d,f);
    M(a,c,_121665);
    A(a,a,d);
    M(c,c,a);
    M(a,d,f);
    M(d,b,x);
    S(b,e);
    sel25519(a,b,r);
    sel25519(c,d,r);
  }
  FOR(i,16) {
    x[i+16]=a[i];
    x[i+32]=c[i];
    x[i+48]=b[i];
    x[i+64]=d[i];
  }
  inv25519(x+32,x+32);
  M(x+16,x+16,x+32);
  pack25519(q,x+16);
  return 0;
}
*)

Require Import Tweetnacl.Libs.Export.
(*
Require Export Tweetnacl.Low.Car25519.
Require Export Tweetnacl.Low.Unpack25519.
Require Export Tweetnacl.Low.Sel25519.
Require Import Tweetnacl.Low.A.
Require Import Tweetnacl.Low.Z.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl.Low.GetBit.
Require Import Tweetnacl.Low.Constant.
*)
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

Section ScalarRec.

Variable A : list Z -> list Z -> list Z.
Variable M : list Z -> list Z -> list Z.
Variable Zub : list Z -> list Z -> list Z.
Variable Sq : list Z -> list Z.
Variable _121665: list Z.
Variable Sel25519 : Z -> list Z -> list Z -> list Z.
Variable getbit : Z -> list Z -> Z.

Variable A_length : forall a b, length a = 16 -> length b = 16 -> length (A a b) = 16.
Variable M_length : forall a b, length a = 16 -> length b = 16 -> length (M a b) = 16.
Variable Zub_length : forall a b, length a = 16 -> length b = 16 -> length (Zub a b) = 16.
Variable Sq_length : forall a, length a = 16 -> length (Sq a) = 16.
Variable Sel25519_length : forall b p q, length p = 16 -> length q = 16 -> length (Sel25519 b p q) = 16.
Variable _121665_length : length _121665 = 16.

Open Scope Z.

Variable A_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (A a b) = 16.
Variable M_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (M a b) = 16.
Variable Zub_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (Zub a b) = 16.
Variable Sq_Zlength : forall a, Zlength a = 16 -> Zlength (Sq a) = 16.
Variable Sel25519_Zlength : forall b p q, Zlength p = 16 -> Zlength q = 16 -> Zlength (Sel25519 b p q) = 16.
Variable _121665_Zlength : Zlength _121665 = 16.

Fixpoint montgomery_rec_gen (m : nat) (z a b c d e f x : list Z) : (list Z * list Z * list Z * list Z * list Z * list Z) :=
  match m with
  | 0%nat => (a,b,c,d,e,f)
  | S n => 
      let r := getbit (Z.of_nat (254 - n)) z in
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
      let r := 0 in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      montgomery_rec_gen n z a b c d e f x
    end.

Definition montgomery_step_gen (m:nat) (z a b c d e f x : list Z) : (list Z * list Z * list Z * list Z * list Z * list Z)  :=
      let r := getbit (Z.of_nat (254 - m)) z in
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
      let r := 0 in
      let (a, b) := (Sel25519 r a b, Sel25519 r b a) in
      let (c, d) := (Sel25519 r c d, Sel25519 r d c) in
      (a,b,c,d,e,f)
(*     end. *)
.

Lemma opt_montgomery_rec_step_gen : forall z a b c d e f x n,
  montgomery_rec_gen (S n) z a b c d e f x = 
  montgomery_rec_gen n z 
  (get_a (montgomery_step_gen n z a b c d e f x))
  (get_b (montgomery_step_gen n z a b c d e f x))
  (get_c (montgomery_step_gen n z a b c d e f x))
  (get_d (montgomery_step_gen n z a b c d e f x))
  (get_e (montgomery_step_gen n z a b c d e f x))
  (get_f (montgomery_step_gen n z a b c d e f x))
  x.
Proof.
intros.
simpl ; reflexivity.
Qed.

Close Scope Z.

Local Ltac solve_montgomery_step_gen_length :=
  intros;
  rewrite /montgomery_step_gen;
  rewrite /get_a /get_b /get_c /get_d /get_e /get_f;
  repeat match goal with
    | _ => orewrite Sel25519_length
    | _ => orewrite M_length
    | _ => orewrite Sq_length
    | _ => orewrite A_length
    | _ => orewrite Zub_length
    | _ => orewrite Sel25519_length
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

Open Scope Z.

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
    | _ => orewrite Sel25519_Zlength
  end ; reflexivity.

Lemma get_a_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_a (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_b_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_b (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_c_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_c (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_d_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_d (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_e_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_e (montgomery_step_gen n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_gen_Zlength. Qed.
Lemma get_f_montgomery_step_gen_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
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




End ScalarRec.


