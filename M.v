Require Export SumList.
Require Export ToFF.
Require Export A.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Import ListNotations.

Open Scope Z.

Fixpoint scalarMult a b := match b with
| [] => []
| h :: q => a * h :: scalarMult a q
end.

Lemma scalarMultToFF: forall n a b, ToFF n (scalarMult a b) = a * ToFF n b.
Proof.
intros n a.
induction b ; go.
unfold scalarMult ; fold scalarMult.
rewrite! ToFF_cons.
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

(*
Fixpoint mult_1' a b := match a, b with 
| [],_ => []
| _,[] => []
| ha :: qa, hb :: qb => ha * hb :: sum_list_Z (sum_list_Z (scalarMult ha qb) (scalarMult hb qa))
 (match mult_1' qa qb with 
  | [] => []
  | l => 0 :: l
  end)
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

Fixpoint List_is_eq a b : bool := match a, b with
| [], [] => true
| h1 :: q1, h2 :: q2 => andb (Zeq_bool h1 h2) (List_is_eq q1 q2)
| _,_ => false
end.

Compute List_is_eq (mult_1' [1;1;1;1;1;1;1;1;1] []) (mult_1 [1;1;1;1;1;1;1;1;1] []).
Compute List_is_eq (mult_1' [0] [0]) (mult_1 [0] [0]).
*)
Fixpoint mult_2 a := match a with 
| [] => []
| h :: q => h + 38 * (nth 15 q 0) :: mult_2 q
end.

Fixpoint mult_3 (a:list Z) : list Z := slice 16 a.

Definition M a b :=
  let m1 := mult_1 a b in
    let m2 := mult_2 m1 in
      mult_3 m2.

Lemma MultToFF' : forall n a b c, mult_1 a b = c -> ToFF n a * ToFF n b = ToFF n c.
Proof.
intro n ; induction a, b ; intros c Hc.
- simpl in *; go.
- simpl in *; go.
- simpl in Hc.
  rewrite Z.mul_comm.
  go.
- rewrite! ToFF_cons.
  unfold mult_1 in Hc; fold mult_1 in Hc.
  SearchAbout Z.mul.
  rewrite <- Zred_factor4.
  rewrite Z.mul_comm.
  rewrite <- Zred_factor4.
  rewrite <- Hc.
  rewrite ToFF_cons.
  rewrite sumListToFF2.
  assert(IHC:mult_1 a0 (z::b) = mult_1 a0 (z::b)) by go.
  apply IHa in IHC.
  rewrite <- IHC.
  rewrite ToFF_cons.
  rewrite Z.mul_comm.
  rewrite Zplus_assoc_reverse.
  f_equal.
  rewrite scalarMultToFF.
  ring.
Qed.

