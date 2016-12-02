Require Export Libs.
Open Scope Z.

Definition Zmin_quad (c1 c2 c3 c4: Z) : Z:=
  let m := match c1 ?= c2 with
           | Eq => c1
           | Lt => c1
           | Gt => c2
         end
   in
   let m' := match c3 ?= c4 with 
           | Eq => c3
           | Lt => c3
           | Gt => c4
         end
   in match m ?= m' with
           | Eq => m
           | Lt => m
           | Gt => m'
         end.

Ltac deal_with_it H := intros ; unfold H ; flatten ; flatten Eq ; try rewrite Z.compare_eq_iff in * ; try rewrite Z.compare_lt_iff in * ; try rewrite Z.compare_gt_iff in * ; go.

Lemma Zmin_quad_1 : forall (x y z t: Z),
  x <= y -> x <= z -> x <= t -> Zmin_quad x y z t = x.
Proof. deal_with_it Zmin_quad. Qed.

Lemma Zmin_quad_2 : forall (x y z t: Z),
  x <= y -> x <= z -> x <= t -> Zmin_quad y x z t = x.
Proof. deal_with_it Zmin_quad. Qed.

Lemma Zmin_quad_3 : forall (x y z t: Z),
  x <= y -> x <= z -> x <= t -> Zmin_quad y z x t = x.
Proof. deal_with_it Zmin_quad. Qed.

Lemma Zmin_quad_4 : forall (x y z t: Z),
  x <= y -> x <= z -> x <= t -> Zmin_quad y z t x = x.
Proof. deal_with_it Zmin_quad. Qed.

Definition Zmax_quad (c1 c2 c3 c4: Z) : Z:=
  let m := match c1 ?= c2 with
           | Eq => c1
           | Lt => c2
           | Gt => c1
         end
   in
   let m' := match c3 ?= c4 with 
           | Eq => c3
           | Lt => c4
           | Gt => c3
         end
   in match m ?= m' with
           | Eq => m
           | Lt => m'
           | Gt => m
         end.

Lemma Zmax_quad_1 : forall (x y z t: Z),
  x >= y -> x >= z -> x >= t -> Zmax_quad x y z t = x.
Proof. deal_with_it Zmax_quad. Qed.

Lemma Zmax_quad_2 : forall (x y z t: Z),
  x >= y -> x >= z -> x >= t -> Zmax_quad y x z t = x.
Proof. deal_with_it Zmax_quad. Qed.

Lemma Zmax_quad_3 : forall (x y z t: Z),
  x >= y -> x >= z -> x >= t -> Zmax_quad y z x t = x.
Proof. deal_with_it Zmax_quad. Qed.

Lemma Zmax_quad_4 : forall (x y z t: Z),
  x >= y -> x >= z -> x >= t -> Zmax_quad y z t x = x.
Proof. deal_with_it Zmax_quad. Qed.