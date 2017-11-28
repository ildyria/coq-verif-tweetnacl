(* (*
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
Require Import Tweetnacl.Low.Car25519.
Require Import Tweetnacl.Low.Unpack25519.
Require Import Tweetnacl.Low.Sel25519.
Require Import Tweetnacl.Low.A.
Require Import Tweetnacl.Low.Z.
Require Import Tweetnacl.Low.M.
Require Import Tweetnacl.Low.S.
Require Import Tweetnacl.Low.GetBit.
Require Import Tweetnacl.Low.Constant.
Require Import Tweetnacl.Low.Get_abcdef.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Low.ScalarMult_rev_fn_gen.

Definition fa := fa A M Zub Sq Sel25519.
Definition fb := fb A M Zub Sq Sel25519.
Definition fc := fc A M Zub Sq c_121665 Sel25519.
Definition fd := fd A M Zub Sq c_121665 Sel25519.
Definition fe := fe A M Zub Sel25519.
Definition ff := ff Zub Sq Sel25519.

Local Ltac solve_dependencies_length :=
  match goal with
    | _ => apply Sel25519_Zlength
    | _ => apply M_Zlength
    | _ => apply Sq_Zlength
    | _ => apply A_Zlength
    | _ => apply Zub_Zlength
    | _ => apply Zlength_c_121665
  end.

Local Ltac solve_dependencies_bound := 
repeat match goal with
  | _ => assumption
  | _ => reflexivity
  | _ => solve_dependencies_length
  | _ => apply M_bound_Zlength
  | _ => apply Sq_bound_Zlength
  | _ => apply A_bound_Zlength_le
  | _ => apply A_bound_Zlength_lt
  | _ => apply Zub_bound_Zlength_lt
  | _ => apply Zub_bound_Zlength_le
  | _ => apply Sel25519_bound_le
  | _ => apply Sel25519_bound_lt_le_id
  | _ => apply Sel25519_bound_lt_lt_id
  | _ => apply Sel25519_bound_le_lt_trans_le_id
  | _ => apply c_121665_bounds
end.

Open Scope Z.

Definition montgomery_fn := abstract_fn_rev fa fb fc fd fe ff getbit.

Lemma montgomery_fn_equation: forall (m p : ℤ) (z a b c d e f x : list ℤ),
       montgomery_fn m p z a b c d e f x =
       (if m <=? 0
        then (a, b, c, d, e, f)
        else
         let (p0, f0) := montgomery_fn (m - 1) p z a b c d e f x in
         let (p1, e0) := p0 in
         let (p2, d0) := p1 in
         let (p3, c0) := p2 in
         let (a0, b0) := p3 in
         (fa (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, fb (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         fc (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, fd (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         fe (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, ff (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x)).
Proof. apply abstract_fn_rev_equation. Qed.

Lemma montgomery_fn_0 : forall p z a b c d e f x,
  montgomery_fn 0 p z a b c d e f x = (a,b,c,d,e,f).
Proof. apply abstract_fn_rev_0. Qed.

Lemma montgomery_fn_n : forall (m p : ℤ) (z a b c d e f x : list ℤ),
       0 < m ->
       montgomery_fn m p z a b c d e f x =
         let (p0, f0) := montgomery_fn (m - 1) p z a b c d e f x in
         let (p1, e0) := p0 in
         let (p2, d0) := p1 in
         let (p3, c0) := p2 in
         let (a0, b0) := p3 in
         (fa (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, fb (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         fc (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, fd (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x,
         fe (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x, ff (getbit (p - (m - 1)) z) a0 b0 c0 d0 e0 f0 x).
Proof. apply abstract_fn_rev_n. Qed.

(* Lemma opt_montgomery_rec_step : forall n z a b c d e f x,
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

 *)
Lemma opt_montgomery_rec_step_ext : forall n z a b c d e f e' f' x,
  montgomery_rec (S n) z a b c d e' f' x = 
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
apply opt_montgomery_rec_step_gen_ext.
Qed.

Close Scope Z.

Local Ltac Local_solve_montgomery_op_Zlength :=
  repeat match goal with
    | _ => rewrite Zlength_map
    | _ => rewrite Sel25519_Zlength
    | _ => rewrite M_Zlength
    | _ => rewrite Sq_Zlength
    | _ => rewrite A_Zlength
    | _ => rewrite Zub_Zlength
    | _ => omega
  end ; reflexivity.


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

Lemma get_a_montgomery_rec_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_a (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_b_montgomery_rec_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_b (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_c_montgomery_rec_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_c (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_d_montgomery_rec_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_d (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_e_montgomery_rec_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_e (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.
Lemma get_f_montgomery_rec_Zlength : forall n z a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 ->
  Zlength x = 16 ->
  Zlength (get_f (montgomery_rec n z a b c d e f x)) = 16.
Proof. solve_montgomery_rec_Zlength. Qed.

Local Ltac solve_montgomery_step_bound := 
match goal with
  | _ => reflexivity
  | _ => apply A_Zlength
  | _ => apply M_Zlength
  | _ => apply Zub_Zlength
  | _ => apply Sq_Zlength
  | _ => apply Sel25519_Zlength
  | _ => apply M_bound_Zlength
  | _ => apply Sq_bound_Zlength
  | _ => apply A_bound_Zlength_le
  | _ => apply A_bound_Zlength_lt
  | _ => apply Zub_bound_Zlength_lt
  | _ => apply Sel25519_bound_lt_le_id ; assumption
  | _ => apply Sel25519_bound_lt_lt_id ; assumption
  | _ => apply Sel25519_bound_le_lt_trans_le_id ; assumption
end.

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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (montgomery_step  n z a b c d e f x)).
Proof.
apply get_a_montgomery_step_bound ; solve_montgomery_step_bound.
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (montgomery_step  n z a b c d e f x)).
Proof.
apply get_b_montgomery_step_bound ; solve_montgomery_step_bound.
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (montgomery_step  n z a b c d e f x)).
Proof.
apply get_c_montgomery_step_bound ; try solve_montgomery_step_bound.
change (2^16) with 65536; repeat apply Forall_cons; try omega ; apply Forall_nil.
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (montgomery_step  n z a b c d e f x)).
Proof.
apply get_d_montgomery_step_bound ; try solve_montgomery_step_bound.
change (2^16) with 65536; repeat apply Forall_cons; try omega ; apply Forall_nil.
Qed.

Lemma get_a_montgomery_rec_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (montgomery_rec  n z a b c d e f x)).
Proof.
apply get_a_montgomery_rec_gen_bound ; try solve_montgomery_step_bound.
change (2^16) with 65536; repeat apply Forall_cons; try omega ; apply Forall_nil.
Qed.

Lemma get_b_montgomery_rec_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (montgomery_rec  n z a b c d e f x)).
Proof.
apply get_b_montgomery_rec_gen_bound ; try solve_montgomery_step_bound.
change (2^16) with 65536; repeat apply Forall_cons; try omega ; apply Forall_nil.
Qed.

Lemma get_c_montgomery_rec_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (montgomery_rec  n z a b c d e f x)).
Proof.
apply get_c_montgomery_rec_gen_bound ; try solve_montgomery_step_bound.
change (2^16) with 65536; repeat apply Forall_cons; try omega ; apply Forall_nil.
Qed.

Lemma get_d_montgomery_rec_bound : forall n z a b c d e f x,
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (montgomery_rec  n z a b c d e f x)).
Proof.
apply get_d_montgomery_rec_gen_bound ; try solve_montgomery_step_bound.
change (2^16) with 65536; repeat apply Forall_cons; try omega ; apply Forall_nil.
Qed.

Ltac solve_montgomery_op_Zlength :=
  repeat match goal with
    | _ => omega
    | _ => rewrite Zlength_map
    | _ => rewrite Sel25519_Zlength
    | _ => rewrite M_Zlength
    | _ => rewrite Sq_Zlength
    | _ => rewrite A_Zlength
    | _ => rewrite Zub_Zlength
    | _ => rewrite get_a_montgomery_step_Zlength
    | _ => rewrite get_b_montgomery_step_Zlength
    | _ => rewrite get_c_montgomery_step_Zlength
    | _ => rewrite get_d_montgomery_step_Zlength
    | _ => rewrite get_e_montgomery_step_Zlength
    | _ => rewrite get_f_montgomery_step_Zlength
    | _ => rewrite get_a_montgomery_rec_Zlength
    | _ => rewrite get_b_montgomery_rec_Zlength
    | _ => rewrite get_c_montgomery_rec_Zlength
    | _ => rewrite get_d_montgomery_rec_Zlength
    | _ => rewrite get_e_montgomery_rec_Zlength
    | _ => rewrite get_f_montgomery_rec_Zlength
  end ; reflexivity.

Close Scope Z. *)