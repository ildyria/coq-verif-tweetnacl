Require Export SumList.
Require Export ToFF.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
Import ListNotations.

Open Scope Z.

Fixpoint scalarMult a b := match b with
| [] => []
| h :: q => a * h :: scalarMult a q
end.

Fixpoint mult_1 a b := match a with 
| [] => []
| ha :: qa => match b with 
  | [] => []
  | hb :: qb => ha * hb :: sum_list_Z (scalarMult ha qb) (mult_1 qa (hb :: qb))
  end
end.

Fixpoint mult_2 a := match a with 
| [] => []
| h :: q => h + 38 * (nth 15 q 0) :: mult_2 q
end.

Fixpoint mult_3 (a:list Z) : list Z := slice 16 a.

Definition M a b :=
  let m1 := mult_1 a b in
    let m2 := mult_2 m1 in
    mult_3 m2.



