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
Require Import Tweetnacl.Low.AMZubSqSel.
Require Import Tweetnacl.Low.ScalarMult_gen_small.
Require Import Tweetnacl.Gen.abstract_fn_rev.
Require Import Tweetnacl.Low.ScalarMult_rev_fn_gen.
Require Import Tweetnacl.Gen.ABCDEF.

Section ScalarGen.

Open Scope Z.

(*
  Ops.
  A : T -> T -> T;
  M : T -> T -> T;
  Zub : T -> T -> T;
  Sq : T -> T;
  _121665: T;
  Sel25519 : Z -> T -> T -> T;
  getbit : Z -> T -> Z;
*)
Local Instance List_Z_Ops : Ops (list Z) := Build_Ops (list Z) A.A M.M Z.Zub S.Sq c_121665 Sel25519.Sel25519 GetBit.getbit.
Local Instance List_Z_Ops_Prop : Ops_Prop :=  Build_Ops_Prop
  List_Z_Ops
  A.A_Zlength
  M.M_Zlength
  Z.Zub_Zlength
  S.Sq_Zlength
  Sel25519.Sel25519_Zlength
  Constant.Zlength_c_121665
  M.M_bound_Zlength
  S.Sq_bound_Zlength
  A.A_bound_Zlength_le
  A.A_bound_Zlength_lt
  Z.Zub_bound_Zlength_le
  Z.Zub_bound_Zlength_lt
  Sel25519.Sel25519_bound_le
  Sel25519.Sel25519_bound_lt_trans_le
  Sel25519.Sel25519_bound_lt
  Sel25519.Sel25519_bound_lt_le_id
  Sel25519.Sel25519_bound_lt_lt_id
  Sel25519.Sel25519_bound_le_le_id
  Sel25519.Sel25519_bound_le_lt_trans_le_id
  c_121665_bounds.

Local Ltac solve_dependencies_Zlength :=
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
(*   | _ => solve_dependencies_length *)
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

Definition montgomery_fn := abstract_fn_rev.

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

(* Lemma fa_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fa r a b c d e f x) = 16.
Proof. apply fa_Zlength ; solve_dependencies_Zlength. Qed.
Lemma fb_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fb r a b c d e f x) = 16.
Proof. apply fb_Zlength ; solve_dependencies_Zlength. Qed.
Lemma fc_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fc r a b c d e f x) = 16.
Proof. apply fc_Zlength ; solve_dependencies_Zlength. Qed.
Lemma fd_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fd r a b c d e f x) = 16.
Proof. apply fd_Zlength ; solve_dependencies_Zlength. Qed.
Lemma fe_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fe r a b c d e f x) = 16.
Proof. apply fe_Zlength ; solve_dependencies_Zlength. Qed.
Lemma ff_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (ff r a b c d e f x) = 16.
Proof. apply ff_Zlength ; solve_dependencies_Zlength. Qed. *)

Local Ltac solve_f_length :=
  repeat match goal with
    | _ => assumption
    | |- Zlength (fa _ _ _ _ _ _ _ _) = _ => apply fa_Zlength
    | |- Zlength (fb _ _ _ _ _ _ _ _) = _ => apply fb_Zlength
    | |- Zlength (fc _ _ _ _ _ _ _ _) = _ => apply fc_Zlength
    | |- Zlength (fd _ _ _ _ _ _ _ _) = _ => apply fd_Zlength
    | |- Zlength (fe _ _ _ _ _ _ _ _) = _ => apply fe_Zlength
    | |- Zlength (ff _ _ _ _ _ _ _ _) = _ => apply ff_Zlength
    | _ => idtac
  end.
(* 
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
Proof. apply fa_bound ; solve_dependencies_bound. Qed.
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
Proof. apply fb_bound ; solve_dependencies_bound. Qed.
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
    Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fc r a b c d e f x).
Proof. apply fc_bound ; solve_dependencies_bound. Qed.
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
    Forall (fun x0 : ℤ => 0 <= x0 < 2 ^ 16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (fd r a b c d e f x).
Proof. apply fd_bound ; solve_dependencies_bound. Qed.
 *)
Local Ltac solve_f_bound :=
  repeat match goal with
    | _ => assumption
    | |- Forall _ (fa _ _ _ _ _ _ _ _)  => apply fa_bound
    | |- Forall _ (fb _ _ _ _ _ _ _ _)  => apply fb_bound
    | |- Forall _ (fc _ _ _ _ _ _ _ _)  => apply fc_bound
    | |- Forall _ (fd _ _ _ _ _ _ _ _)  => apply fd_bound
    | _ => idtac
  end.

Lemma fa_step : forall n p z a b c d e f x ,
  0 <= n ->
   fa (getbit (p - n) z)
     (get_a (montgomery_fn n p z a b c d e f x))
     (get_b (montgomery_fn n p z a b c d e f x))
     (get_c (montgomery_fn n p z a b c d e f x))
     (get_d (montgomery_fn n p z a b c d e f x))
     (get_e (montgomery_fn n p z a b c d e f x))
     (get_f (montgomery_fn n p z a b c d e f x)) x =
   get_a (montgomery_fn (n + 1) p z a b c d e f x).
Proof. apply abstract_fn_a. Qed.
Lemma fb_step : forall n p z a b c d e f x ,
  0 <= n ->
   fb (getbit (p - n) z)
     (get_a (montgomery_fn n p z a b c d e f x))
     (get_b (montgomery_fn n p z a b c d e f x))
     (get_c (montgomery_fn n p z a b c d e f x))
     (get_d (montgomery_fn n p z a b c d e f x))
     (get_e (montgomery_fn n p z a b c d e f x))
     (get_f (montgomery_fn n p z a b c d e f x)) x =
   get_b (montgomery_fn (n + 1) p z a b c d e f x).
Proof. apply abstract_fn_b. Qed.
Lemma fc_step : forall n p z a b c d e f x ,
  0 <= n ->
   fc (getbit (p - n) z)
     (get_a (montgomery_fn n p z a b c d e f x))
     (get_b (montgomery_fn n p z a b c d e f x))
     (get_c (montgomery_fn n p z a b c d e f x))
     (get_d (montgomery_fn n p z a b c d e f x))
     (get_e (montgomery_fn n p z a b c d e f x))
     (get_f (montgomery_fn n p z a b c d e f x)) x =
   get_c (montgomery_fn (n + 1) p z a b c d e f x).
Proof. apply abstract_fn_c. Qed.
Lemma fd_step : forall n p z a b c d e f x ,
  0 <= n ->
   fd (getbit (p - n) z)
     (get_a (montgomery_fn n p z a b c d e f x))
     (get_b (montgomery_fn n p z a b c d e f x))
     (get_c (montgomery_fn n p z a b c d e f x))
     (get_d (montgomery_fn n p z a b c d e f x))
     (get_e (montgomery_fn n p z a b c d e f x))
     (get_f (montgomery_fn n p z a b c d e f x)) x =
   get_d (montgomery_fn (n + 1) p z a b c d e f x).
Proof. apply abstract_fn_d. Qed.
Lemma fe_step : forall n p z a b c d e f x ,
  0 <= n ->
   fe (getbit (p - n) z)
     (get_a (montgomery_fn n p z a b c d e f x))
     (get_b (montgomery_fn n p z a b c d e f x))
     (get_c (montgomery_fn n p z a b c d e f x))
     (get_d (montgomery_fn n p z a b c d e f x))
     (get_e (montgomery_fn n p z a b c d e f x))
     (get_f (montgomery_fn n p z a b c d e f x)) x =
   get_e (montgomery_fn (n + 1) p z a b c d e f x).
Proof. apply abstract_fn_e. Qed.
Lemma ff_step : forall n p z a b c d e f x ,
  0 <= n ->
   ff (getbit (p - n) z)
     (get_a (montgomery_fn n p z a b c d e f x))
     (get_b (montgomery_fn n p z a b c d e f x))
     (get_c (montgomery_fn n p z a b c d e f x))
     (get_d (montgomery_fn n p z a b c d e f x))
     (get_e (montgomery_fn n p z a b c d e f x))
     (get_f (montgomery_fn n p z a b c d e f x)) x =
   get_f (montgomery_fn (n + 1) p z a b c d e f x).
Proof. apply abstract_fn_f. Qed.

Lemma get_a_montgomery_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_a (montgomery_fn n p z a b c d e f x)) = 16.
Proof. apply get_a_abstract_fn_Zlength ; intros; solve_f_length. Qed.
Lemma get_b_montgomery_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_b (montgomery_fn n p z a b c d e f x)) = 16.
Proof. apply get_b_abstract_fn_Zlength ; intros; solve_f_length. Qed.
Lemma get_c_montgomery_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_c (montgomery_fn n p z a b c d e f x)) = 16.
Proof. apply get_c_abstract_fn_Zlength ; intros; solve_f_length. Qed.
Lemma get_d_montgomery_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_d (montgomery_fn n p z a b c d e f x)) = 16.
Proof. apply get_d_abstract_fn_Zlength ; intros; solve_f_length. Qed.
Lemma get_e_montgomery_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_e (montgomery_fn n p z a b c d e f x)) = 16.
Proof. apply get_e_abstract_fn_Zlength ; intros; solve_f_length. Qed.
Lemma get_f_montgomery_fn_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_f (montgomery_fn n p z a b c d e f x)) = 16.
Proof. apply get_f_abstract_fn_Zlength ; intros; solve_f_length. Qed.

Lemma get_a_montgomery_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (montgomery_fn n p z a b c d e f x)).
Proof. apply get_a_abstract_fn_bound; intros; solve_f_bound ; solve_f_length. Qed.
Lemma get_b_montgomery_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (montgomery_fn n p z a b c d e f x)).
Proof. apply get_b_abstract_fn_bound; intros; solve_f_bound ; solve_f_length. Qed.

Lemma get_c_montgomery_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (montgomery_fn n p z a b c d e f x)).
Proof. apply get_c_abstract_fn_bound; intros; solve_f_bound ; solve_f_length. Qed.

Lemma get_d_montgomery_fn_bound : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 ->
  Zlength b = 16 ->
  Zlength c = 16 ->
  Zlength d = 16 ->
  Zlength e = 16 ->
  Zlength f = 16 ->
  Zlength x = 16 ->
    Forall (fun x => -38 <= x < 2^16 + 38) a ->
    Forall (fun x => -38 <= x < 2^16 + 38) b ->
    Forall (fun x => -38 <= x < 2^16 + 38) c ->
    Forall (fun x => -38 <= x < 2^16 + 38) d ->
    Forall (fun x => 0 <= x < 2^16) x ->
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (montgomery_fn n p z a b c d e f x)).
Proof. apply get_d_abstract_fn_bound; intros; solve_f_bound ; solve_f_length. Qed.

Ltac solve_montgomery_rec_rev_Zlength :=
  repeat match goal with
    | _ => omega
    | _ => rewrite Zlength_map
    | _ => rewrite Sel25519_Zlength
    | _ => rewrite M_Zlength
    | _ => rewrite Sq_Zlength
    | _ => rewrite A_Zlength
    | _ => rewrite Zub_Zlength
    | _ => rewrite fa_Zlength
    | _ => rewrite fb_Zlength
    | _ => rewrite fc_Zlength
    | _ => rewrite fd_Zlength
    | _ => rewrite fe_Zlength
    | _ => rewrite ff_Zlength
    | _ => rewrite get_a_montgomery_fn_Zlength
    | _ => rewrite get_b_montgomery_fn_Zlength
    | _ => rewrite get_c_montgomery_fn_Zlength
    | _ => rewrite get_d_montgomery_fn_Zlength
    | _ => rewrite get_e_montgomery_fn_Zlength
    | _ => rewrite get_f_montgomery_fn_Zlength
  end ; try reflexivity.

Close Scope Z.

End ScalarGen.