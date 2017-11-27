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
(* Require Import Tweetnacl.Low.ScalarMult_rev_gen. *)
Require Import Tweetnacl.Low.ScalarMult_rev_gen_fn.

Definition montgomery_rec_rev := abstract_fn_rev A M Zub Sq c_121665 Sel25519 getbit.

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

Lemma fa_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fa r a b c d e f x) = 16.
Proof. apply (fa_Zlength _ _ _ _ c_121665) ; solve_dependencies_length. Qed.
Lemma fb_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fb r a b c d e f x) = 16.
Proof. apply (fb_Zlength _ _ _ _ c_121665) ; solve_dependencies_length. Qed.
Lemma fc_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fc r a b c d e f x) = 16.
Proof. apply (fc_Zlength _ _ _ _ c_121665) ; solve_dependencies_length. Qed.
Lemma fd_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fd r a b c d e f x) = 16.
Proof. apply (fd_Zlength _ _ _ _ c_121665) ; solve_dependencies_length. Qed.
Lemma fe_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (fe r a b c d e f x) = 16.
Proof. apply (fe_Zlength _ _ _ c_121665) ; solve_dependencies_length. Qed.
Lemma ff_Zlength : forall r a b c d e f x,
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (ff r a b c d e f x) = 16.
Proof. apply (ff_Zlength _ _ c_121665) ; solve_dependencies_length. Qed.

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
Proof. apply (fa_bound _ _ _ _ c_121665) ; solve_dependencies_bound. Qed.
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
Proof. apply (fb_bound _ _ _ _ c_121665) ; solve_dependencies_bound. Qed.
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
Proof. apply (fc_bound _ _ _ _ c_121665) ; solve_dependencies_bound. Qed.
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
Proof. apply (fd_bound _ _ _ _ c_121665) ; solve_dependencies_bound. Qed.

Local Ltac solve_eq_gen_rec := 
  intros; by rewrite /fa /fb /fc /fd /fe /ff /montgomery_rec_rev 
  ?abstract_fn_a  ?abstract_fn_b  ?abstract_fn_c
   ?abstract_fn_d  ?abstract_fn_e  ?abstract_fn_f ; try omega.

Lemma fa_step : forall p n z a b c d e f x ,
  0 <= n ->
   fa (getbit (p - n) z)
     (get_a (montgomery_rec_rev n p z a b c d e f x))
     (get_b (montgomery_rec_rev n p z a b c d e f x))
     (get_c (montgomery_rec_rev n p z a b c d e f x))
     (get_d (montgomery_rec_rev n p z a b c d e f x))
     (get_e (montgomery_rec_rev n p z a b c d e f x))
     (get_f (montgomery_rec_rev n p z a b c d e f x)) x =
   get_a (montgomery_rec_rev (n + 1) p z a b c d e f x).
Proof. solve_eq_gen_rec. Qed.
Lemma fb_step : forall p n z a b c d e f x ,
  0 <= n ->
   fb (getbit (p - n) z)
     (get_a (montgomery_rec_rev n p z a b c d e f x))
     (get_b (montgomery_rec_rev n p z a b c d e f x))
     (get_c (montgomery_rec_rev n p z a b c d e f x))
     (get_d (montgomery_rec_rev n p z a b c d e f x))
     (get_e (montgomery_rec_rev n p z a b c d e f x))
     (get_f (montgomery_rec_rev n p z a b c d e f x)) x =
   get_b (montgomery_rec_rev (n + 1) p z a b c d e f x).
Proof. solve_eq_gen_rec. Qed.
Lemma fc_step : forall p n z a b c d e f x ,
  0 <= n ->
   fc (getbit (p - n) z)
     (get_a (montgomery_rec_rev n p z a b c d e f x))
     (get_b (montgomery_rec_rev n p z a b c d e f x))
     (get_c (montgomery_rec_rev n p z a b c d e f x))
     (get_d (montgomery_rec_rev n p z a b c d e f x))
     (get_e (montgomery_rec_rev n p z a b c d e f x))
     (get_f (montgomery_rec_rev n p z a b c d e f x)) x =
   get_c (montgomery_rec_rev (n + 1) p z a b c d e f x).
Proof. solve_eq_gen_rec. Qed.
Lemma fd_step : forall p n z a b c d e f x ,
  0 <= n ->
   fd (getbit (p - n) z)
     (get_a (montgomery_rec_rev n p z a b c d e f x))
     (get_b (montgomery_rec_rev n p z a b c d e f x))
     (get_c (montgomery_rec_rev n p z a b c d e f x))
     (get_d (montgomery_rec_rev n p z a b c d e f x))
     (get_e (montgomery_rec_rev n p z a b c d e f x))
     (get_f (montgomery_rec_rev n p z a b c d e f x)) x =
   get_d (montgomery_rec_rev (n + 1) p z a b c d e f x).
Proof. solve_eq_gen_rec. Qed.
Lemma fe_step : forall p n z a b c d e f x ,
  0 <= n ->
   fe (getbit (p - n) z)
     (get_a (montgomery_rec_rev n p z a b c d e f x))
     (get_b (montgomery_rec_rev n p z a b c d e f x))
     (get_c (montgomery_rec_rev n p z a b c d e f x))
     (get_d (montgomery_rec_rev n p z a b c d e f x))
     (get_e (montgomery_rec_rev n p z a b c d e f x))
     (get_f (montgomery_rec_rev n p z a b c d e f x)) x =
   get_e (montgomery_rec_rev (n + 1) p z a b c d e f x).
Proof. solve_eq_gen_rec. Qed.
Lemma ff_step : forall p n z a b c d e f x ,
  0 <= n ->
   ff (getbit (p - n) z)
     (get_a (montgomery_rec_rev n p z a b c d e f x))
     (get_b (montgomery_rec_rev n p z a b c d e f x))
     (get_c (montgomery_rec_rev n p z a b c d e f x))
     (get_d (montgomery_rec_rev n p z a b c d e f x))
     (get_e (montgomery_rec_rev n p z a b c d e f x))
     (get_f (montgomery_rec_rev n p z a b c d e f x)) x =
   get_f (montgomery_rec_rev (n + 1) p z a b c d e f x).
Proof. solve_eq_gen_rec. Qed.

Lemma get_a_montgomery_rec_rev_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_a (montgomery_rec_rev n p z a b c d e f x)) = 16.
Proof. apply get_a_abstract_fn_Zlength ; solve_dependencies_length. Qed.
Lemma get_b_montgomery_rec_rev_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_b (montgomery_rec_rev n p z a b c d e f x)) = 16.
Proof. apply get_b_abstract_fn_Zlength ; solve_dependencies_length. Qed.
Lemma get_c_montgomery_rec_rev_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_c (montgomery_rec_rev n p z a b c d e f x)) = 16.
Proof. apply get_c_abstract_fn_Zlength ; solve_dependencies_length. Qed.
Lemma get_d_montgomery_rec_rev_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_d (montgomery_rec_rev n p z a b c d e f x)) = 16.
Proof. apply get_d_abstract_fn_Zlength ; solve_dependencies_length. Qed.
Lemma get_e_montgomery_rec_rev_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_e (montgomery_rec_rev n p z a b c d e f x)) = 16.
Proof. apply get_e_abstract_fn_Zlength ; solve_dependencies_length. Qed.
Lemma get_f_montgomery_rec_rev_Zlength : forall n p z a b c d e f x,
  0 <= n ->
  Zlength a = 16 -> Zlength b = 16 -> Zlength c = 16 ->
  Zlength d = 16 -> Zlength e = 16 -> Zlength f = 16 -> Zlength x = 16 ->
  Zlength (get_f (montgomery_rec_rev n p z a b c d e f x)) = 16.
Proof. apply get_f_abstract_fn_Zlength ; solve_dependencies_length. Qed.

Lemma get_a_montgomery_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_a (montgomery_rec_rev n p z a b c d e f x)).
Proof. apply get_a_abstract_rec_rev_bound; solve_dependencies_bound. Qed.

Lemma get_b_montgomery_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_b (montgomery_rec_rev n p z a b c d e f x)).
Proof. apply get_b_abstract_rec_rev_bound; solve_dependencies_bound. Qed.

Lemma get_c_montgomery_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_c (montgomery_rec_rev n p z a b c d e f x)).
Proof. apply get_c_abstract_rec_rev_bound ; solve_dependencies_bound. Qed.

Lemma get_d_montgomery_rec_rev_bound : forall n p z a b c d e f x,
  0 <= n ->
  0 <= p ->
  n <= p + 1 ->
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
    Forall (fun x => -38 <= x < 2^16 + 38) (get_d (montgomery_rec_rev n p z a b c d e f x)).
Proof. apply get_d_abstract_rec_rev_bound ; solve_dependencies_bound. Qed.

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
    | _ => rewrite get_a_montgomery_rec_rev_Zlength
    | _ => rewrite get_b_montgomery_rec_rev_Zlength
    | _ => rewrite get_c_montgomery_rec_rev_Zlength
    | _ => rewrite get_d_montgomery_rec_rev_Zlength
    | _ => rewrite get_e_montgomery_rec_rev_Zlength
    | _ => rewrite get_f_montgomery_rec_rev_Zlength
  end ; try reflexivity.

Close Scope Z.