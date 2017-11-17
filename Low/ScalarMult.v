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
Require Export Tweetnacl.Low.Car25519.
Require Export Tweetnacl.Low.Unpack25519.
Require Export Tweetnacl.Low.Sel25519.
Require Import Tweetnacl.Low.A.
Require Import Tweetnacl.Low.Z.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl.Low.GetBit.
Require Import Tweetnacl.Low.Constant.
Require Export Tweetnacl.Low.ScalarMult_gen.

Open Scope Z.

Definition montgomery_step := montgomery_step_gen A M Zub Sq _121665 Sel25519 getbit.
Definition montgomery_rec := montgomery_rec_gen A M Zub Sq _121665 Sel25519 getbit.

Lemma opt_montgomery_rec_step : forall z a b c d e f x n,
  montgomery_rec (S n) z a b c d e f x = 
  montgomery_rec n z 
  (get_a (montgomery_step n z a b c d e f x))
  (get_b (montgomery_step n z a b c d e f x))
  (get_c (montgomery_step n z a b c d e f x))
  (get_d (montgomery_step n z a b c d e f x))
  (get_e (montgomery_step n z a b c d e f x))
  (get_f (montgomery_step n z a b c d e f x))
  x.
Proof.
rewrite /montgomery_rec /montgomery_step.
apply opt_montgomery_rec_step_gen.
Qed.

Close Scope Z.

Local Ltac solve_montgomery_step_length := 
  intros; rewrite /montgomery_step;
  repeat match goal with
    | _ => apply get_a_montgomery_step_gen_length ; auto
    | _ => apply get_b_montgomery_step_gen_length ; auto
    | _ => apply get_c_montgomery_step_gen_length ; auto
    | _ => apply get_d_montgomery_step_gen_length ; auto
    | _ => apply get_e_montgomery_step_gen_length ; auto
    | _ => apply get_f_montgomery_step_gen_length ; auto
    | _ => apply A_length
    | _ => apply M_length
    | _ => apply Zub_length
    | _ => apply Sq_length
    | _ => apply Sel25519_length
  end.

Lemma get_a_montgomery_step_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_a (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_length. Qed.
Lemma get_b_montgomery_step_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_b (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_length. Qed.
Lemma get_c_montgomery_step_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_c (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_length. Qed.
Lemma get_d_montgomery_step_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_d (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_length. Qed.
Lemma get_e_montgomery_step_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_e (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_length. Qed.
Lemma get_f_montgomery_step_length : forall z a b c d e f x n,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_f (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_length. Qed.

Open Scope Z.

Local Ltac solve_montgomery_step_Zlength := 
  intros; rewrite /montgomery_step;
  repeat match goal with
    | _ => apply get_a_montgomery_step_gen_Zlength ; auto
    | _ => apply get_b_montgomery_step_gen_Zlength ; auto
    | _ => apply get_c_montgomery_step_gen_Zlength ; auto
    | _ => apply get_d_montgomery_step_gen_Zlength ; auto
    | _ => apply get_e_montgomery_step_gen_Zlength ; auto
    | _ => apply get_f_montgomery_step_gen_Zlength ; auto
    | _ => apply A_Zlength
    | _ => apply M_Zlength
    | _ => apply Zub_Zlength
    | _ => apply Sq_Zlength
    | _ => apply Sel25519_Zlength
  end.

Lemma get_a_montgomery_step_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_a (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_Zlength. Qed.
Lemma get_b_montgomery_step_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_b (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_Zlength. Qed.
Lemma get_c_montgomery_step_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_c (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_Zlength. Qed.
Lemma get_d_montgomery_step_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_d (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_Zlength. Qed.
Lemma get_e_montgomery_step_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_e (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_Zlength. Qed.
Lemma get_f_montgomery_step_Zlength : forall z a b c d e f x n,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_f (montgomery_step n z a b c d e f x)) = 16.
Proof. solve_montgomery_step_Zlength. Qed.

Close Scope Z.

Local Ltac solve_montgomery_rec_length := 
  intros; rewrite /montgomery_rec;
  repeat match goal with
    | _ => apply get_a_montgomery_rec_gen_length ; auto
    | _ => apply get_b_montgomery_rec_gen_length ; auto
    | _ => apply get_c_montgomery_rec_gen_length ; auto
    | _ => apply get_d_montgomery_rec_gen_length ; auto
    | _ => apply get_e_montgomery_rec_gen_length ; auto
    | _ => apply get_f_montgomery_rec_gen_length ; auto
    | _ => apply A_length
    | _ => apply M_length
    | _ => apply Zub_length
    | _ => apply Sq_length
    | _ => apply Sel25519_length
  end.

Lemma get_a_montgomery_get_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_a (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_length. Qed.
Lemma get_b_montgomery_get_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_b (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_length. Qed.
Lemma get_c_montgomery_get_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_c (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_length. Qed.
Lemma get_d_montgomery_get_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_d (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_length. Qed.
Lemma get_e_montgomery_get_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_e (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_length. Qed.
Lemma get_f_montgomery_get_length : forall n z a b c d e f x,
  length a = 16 -> length b = 16 -> length c = 16 ->
  length d = 16 -> length e = 16 -> length f = 16 ->
  length x = 16 ->
  length (get_f (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_length. Qed.

Open Scope Z.

Local Ltac solve_montgomery_rec_Zlength := 
  intros; rewrite /montgomery_rec;
  repeat match goal with
    | _ => apply get_a_montgomery_rec_gen_Zlength ; auto
    | _ => apply get_b_montgomery_rec_gen_Zlength ; auto
    | _ => apply get_c_montgomery_rec_gen_Zlength ; auto
    | _ => apply get_d_montgomery_rec_gen_Zlength ; auto
    | _ => apply get_e_montgomery_rec_gen_Zlength ; auto
    | _ => apply get_f_montgomery_rec_gen_Zlength ; auto
    | _ => apply A_Zlength
    | _ => apply M_Zlength
    | _ => apply Zub_Zlength
    | _ => apply Sq_Zlength
    | _ => apply Sel25519_Zlength
  end.

Lemma get_a_montgomery_get_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_a (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_b_montgomery_get_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_b (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_c_montgomery_get_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_c (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_d_montgomery_get_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_d (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_e_montgomery_get_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_e (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_f_montgomery_get_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_f (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.

Close Scope Z.