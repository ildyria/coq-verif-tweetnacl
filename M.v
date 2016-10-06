Require Export SumList.
Require Export ToFF.
Require Export A.
Import ListNotations.

Require Export Tools.
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
rewrite IHb.
ring.
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
| h :: q => h + 38 * (nth 3 q 0) :: mult_2 q
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
  rewrite <- Hc.
  rewrite ToFF_cons.
  rewrite sumListToFF2.
  rewrite <- (IHa (z :: b) (mult_1 a0 (z :: b))) by go.
  rewrite ToFF_cons.
  rewrite scalarMultToFF.
  ring.
Qed.

Lemma SumListTail : forall l, mult_2 l = sum_list_Z l (scalarMult 38 (tail 3 l)).
Proof.
intro l.
Admitted.

Lemma mult_2_ToFF : forall n l, ToFF n (mult_2 l) = ToFF n l + 38 * ToFF n (tail (16%nat) l).
Proof.
intro n.
induction l ; go.
unfold mult_2; fold mult_2.
simpl ; flatten ; flatten Eq0 ; simpl.



Lemma reduce_slice_ToFF: forall l, Z.of_nat (length l) < 30 -> (ToFF 16 (mult_3 (mult_2 l))) mod (Z.pow 2 255 - 19) = (ToFF 16 l) mod (Z.pow 2 255 - 19).
Proof.