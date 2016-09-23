Require Export SumList.
Require Export ToFF.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Import ListNotations.

Open Scope Z.

Fixpoint scalarMult a b := match b with
| [] => []
| h :: q => a * h :: scalarMult a q
end.

Lemma scalarMultToFF: forall a b, ToFF 16 (scalarMult a b) = a * ToFF 16 b.
Proof.
intro a.
induction b ; go.
unfold scalarMult ; fold scalarMult.
rewrite! ToFFCons.
rewrite <- Zred_factor4.
f_equal.
rewrite IHb.
rewrite <- Zmult_assoc_reverse.
rewrite <- Zmult_assoc_reverse.
f_equal.
rewrite Z.mul_comm.
omega.
Qed.

Fixpoint mult_1 a b := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: sum_list_Z (scalarMult ha qb) (mult_1 qa (hb::qb))
end.

Fixpoint mult_1' a b := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: sum_list_Z (sum_list_Z (scalarMult ha qb) (scalarMult hb qa))
(0 :: mult_1' qa qb)
end.

Lemma mult_1'_comm : forall a b, mult_1' a b = mult_1' b a.
Proof.
induction a,b ; go.
unfold mult_1' ; fold mult_1'.
f_equal ; go.
rewrite IHa.
f_equal.
rewrite sum_list_comm ; go.
Qed.

Compute mult_1' [1;1;1;1;1;1;1;1;1] [0;0].

Lemma mult_1'_cons : forall a hb qb, mult_1' a (hb :: qb) = sum_list_Z (scalarMult hb a) (0 :: mult_1' a qb).
Proof.
induction a; intros hb qb ; go.




Lemma mult_1_1' : forall a b, mult_1 a b = mult_1' a b.
Proof.
induction a, b ; go.
unfold mult_1; fold mult_1.
unfold mult_1'; fold mult_1'.
f_equal.
rewrite IHa.

Lemma mult_1_comm: forall a b, 


Fixpoint mult_2 a := match a with 
| [] => []
| h :: q => h + 38 * (nth 15 q 0) :: mult_2 q
end.

Fixpoint mult_3 (a:list Z) : list Z := slice 16 a.

Definition M a b :=
  let m1 := mult_1 a b in
    let m2 := mult_2 m1 in
      mult_3 m2.


Lemma MultToFF : forall a b c, mult_1 a b = c -> ToFF 16 a * ToFF 16 b = ToFF 16 c.
Proof.
induction a, b ; intros c Hc.
- simpl in *; go.
- simpl in *; go.
- simpl in Hc.
  rewrite Z.mul_comm.
  go.
- rewrite! ToFFCons.
  unfold mult_1 in Hc; fold mult_1 in Hc.
  SearchAbout Z.mul.
  rewrite <- Zred_factor4.
  rewrite Z.mul_comm.
  rewrite <- Zred_factor4.
  


