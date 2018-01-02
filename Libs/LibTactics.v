From Tweetnacl Require Export Libs.LibTactics_Rennes.
Require Import ZArith.

Ltac transparent_specialize_one H arg :=
  first [ let test := eval unfold H in H in idtac;
          let H' := fresh in rename H into H'; pose (H' arg) as H; subst H'
         | specialize (H arg) ].

Ltac specialize_by' tac :=
  idtac;
  match goal with
  | [ H : ?A -> ?B |- _ ] =>
    match type of A with
      Prop =>
      let H' := fresh in
      assert (H' : A) by tac;
      transparent_specialize_one H H';
      try clear H' (* if [H] was transparent, [H'] will remain *)
    end
  end.

Ltac specialize_by tac := repeat specialize_by' tac.

Ltac boum :=
  repeat match goal with
    | [ |- context[_ <-> _] ] => progress split
    | [ H : _ /\ _  |- _ ] => progress destruct H
    | [ H : _ \/ _  |- _ ] => progress destruct H
    | _ => progress intros
    | _ => go
   end.

Ltac ind_boum l :=
  induction l ; boum.

Ltac destr_boum n :=
  destruct n ; boum.

Ltac inv_boum H :=
  inversion H ; boum.

Ltac oreplace a b :=
  replace a with b by omega.

Ltac orewrite H :=
  rewrite H ; try omega.

Ltac convert_length_to_Zlength L:=
  intros;
  repeat match goal with
    | [ H : context[Zlength] |- _ ] => progress rewrite Zlength_correct in H
    | [ |- context[Zlength] ] => progress rewrite Zlength_correct
  end ; try (apply L ; go) ; try (rewrite L ; go).

Open Scope Z.

Ltac is_Z n := match n with
  | Z0 => true
  | Z.pos _ => true
  | Z.neg _ => true
  | _ => false
  end.

Ltac Grind_add_Z_ :=
  repeat match goal with
    | |- context[Z.add ?A ?B] =>
    match is_Z A with
      | false => Grind_add_Z_ A
      | true  =>
      match is_Z B with
      | false => Grind_add_Z_ B
      | true  => let C := (eval compute in (Z.add A B)) in
        change (Z.add A B) with C
      end
    end
  end.

Ltac Grind_sub_Z_ :=
  repeat match goal with
    | |- context[Z.sub ?A ?B] =>
    match is_Z A with
      | false => Grind_sub_Z_ A
      | true  =>
      match is_Z B with
      | false => Grind_sub_Z_ B
      | true  => let C := (eval compute in (Z.add A B)) in
        change (Z.sub A B) with C
      end
    end
  end.

Ltac Grind_add_Z := Grind_add_Z_ ; Grind_sub_Z_.

(* Ltac Grind_add_Z :=
  try change (0 + 0)  with 0;
  try change (0 + 1)  with 1;
  try change (0 + 2)  with 2;
  try change (0 + 3)  with 3;
  try change (0 + 4)  with 4;
  try change (0 + 5)  with 5;
  try change (0 + 6)  with 6;
  try change (0 + 7)  with 7;
  try change (0 + 8)  with 8;
  try change (0 + 9)  with 9;
  try change (0 + 10) with 10;
  try change (0 + 11) with 11;
  try change (0 + 12) with 12;
  try change (0 + 13) with 13;
  try change (0 + 14) with 14;
  try change (0 + 15) with 15;
  try change (1 + 0)  with 1;
  try change (1 + 1)  with 2;
  try change (1 + 2)  with 3;
  try change (1 + 3)  with 4;
  try change (1 + 4)  with 5;
  try change (1 + 5)  with 6;
  try change (1 + 6)  with 7;
  try change (1 + 7)  with 8;
  try change (1 + 8)  with 9;
  try change (1 + 9)  with 10;
  try change (1 + 10) with 11;
  try change (1 + 11) with 12;
  try change (1 + 12) with 13;
  try change (1 + 13) with 14;
  try change (1 + 14) with 15;
  try change (1 + 15) with 16;
  try change (2 + 0)  with 2;
  try change (2 + 1)  with 3;
  try change (2 + 2)  with 4;
  try change (2 + 3)  with 5;
  try change (2 + 4)  with 6;
  try change (2 + 5)  with 7;
  try change (2 + 6)  with 8;
  try change (2 + 7)  with 9;
  try change (2 + 8)  with 10;
  try change (2 + 9)  with 11;
  try change (2 + 10) with 12;
  try change (2 + 11) with 13;
  try change (2 + 12) with 14;
  try change (2 + 13) with 15;
  try change (2 + 14) with 16;
  try change (2 + 15) with 17;
  try change (3 + 0)  with 3;
  try change (3 + 1)  with 4;
  try change (3 + 2)  with 5;
  try change (3 + 3)  with 6;
  try change (3 + 4)  with 7;
  try change (3 + 5)  with 8;
  try change (3 + 6)  with 9;
  try change (3 + 7)  with 10;
  try change (3 + 8)  with 11;
  try change (3 + 9)  with 12;
  try change (3 + 10) with 13;
  try change (3 + 11) with 14;
  try change (3 + 12) with 15;
  try change (3 + 13) with 16;
  try change (3 + 14) with 17;
  try change (3 + 15) with 18;
  try change (4 + 0)  with 4;
  try change (4 + 1)  with 5;
  try change (4 + 2)  with 6;
  try change (4 + 3)  with 7;
  try change (4 + 4)  with 8;
  try change (4 + 5)  with 9;
  try change (4 + 6)  with 10;
  try change (4 + 7)  with 11;
  try change (4 + 8)  with 12;
  try change (4 + 9)  with 13;
  try change (4 + 10) with 14;
  try change (4 + 11) with 15;
  try change (4 + 12) with 16;
  try change (4 + 13) with 17;
  try change (4 + 14) with 18;
  try change (4 + 15) with 19;
  try change (5 + 0)  with 5;
  try change (5 + 1)  with 6;
  try change (5 + 2)  with 7;
  try change (5 + 3)  with 8;
  try change (5 + 4)  with 9;
  try change (5 + 5)  with 10;
  try change (5 + 6)  with 11;
  try change (5 + 7)  with 12;
  try change (5 + 8)  with 13;
  try change (5 + 9)  with 14;
  try change (5 + 10) with 15;
  try change (5 + 11) with 16;
  try change (5 + 12) with 17;
  try change (5 + 13) with 18;
  try change (5 + 14) with 19;
  try change (5 + 15) with 20;
  try change (6 + 0)  with 6;
  try change (6 + 1)  with 7;
  try change (6 + 2)  with 8;
  try change (6 + 3)  with 9;
  try change (6 + 4)  with 10;
  try change (6 + 5)  with 11;
  try change (6 + 6)  with 12;
  try change (6 + 7)  with 13;
  try change (6 + 8)  with 14;
  try change (6 + 9)  with 15;
  try change (6 + 10) with 16;
  try change (6 + 11) with 17;
  try change (6 + 12) with 18;
  try change (6 + 13) with 19;
  try change (6 + 14) with 20;
  try change (6 + 15) with 21;
  try change (7 + 0)  with 7;
  try change (7 + 1)  with 8;
  try change (7 + 2)  with 9;
  try change (7 + 3)  with 10;
  try change (7 + 4)  with 11;
  try change (7 + 5)  with 12;
  try change (7 + 6)  with 13;
  try change (7 + 7)  with 14;
  try change (7 + 8)  with 15;
  try change (7 + 9)  with 16;
  try change (7 + 10) with 17;
  try change (7 + 11) with 18;
  try change (7 + 12) with 19;
  try change (7 + 13) with 20;
  try change (7 + 14) with 21;
  try change (7 + 15) with 22;
  try change (8 + 0)  with 8;
  try change (8 + 1)  with 9;
  try change (8 + 2)  with 10;
  try change (8 + 3)  with 11;
  try change (8 + 4)  with 12;
  try change (8 + 5)  with 13;
  try change (8 + 6)  with 14;
  try change (8 + 7)  with 15;
  try change (8 + 8)  with 16;
  try change (8 + 9)  with 17;
  try change (8 + 10) with 18;
  try change (8 + 11) with 19;
  try change (8 + 12) with 20;
  try change (8 + 13) with 21;
  try change (8 + 14) with 22;
  try change (8 + 15) with 23;
  try change (9 + 0)  with 9;
  try change (9 + 1)  with 10;
  try change (9 + 2)  with 11;
  try change (9 + 3)  with 12;
  try change (9 + 4)  with 13;
  try change (9 + 5)  with 14;
  try change (9 + 6)  with 15;
  try change (9 + 7)  with 16;
  try change (9 + 8)  with 17;
  try change (9 + 9)  with 18;
  try change (9 + 10) with 19;
  try change (9 + 11) with 20;
  try change (9 + 12) with 21;
  try change (9 + 13) with 22;
  try change (9 + 14) with 23;
  try change (9 + 15) with 24;
  try change (10 + 0)  with 10;
  try change (10 + 1)  with 11;
  try change (10 + 2)  with 12;
  try change (10 + 3)  with 13;
  try change (10 + 4)  with 14;
  try change (10 + 5)  with 15;
  try change (10 + 6)  with 16;
  try change (10 + 7)  with 17;
  try change (10 + 8)  with 18;
  try change (10 + 9)  with 19;
  try change (10 + 10) with 20;
  try change (10 + 11) with 21;
  try change (10 + 12) with 22;
  try change (10 + 13) with 23;
  try change (10 + 14) with 24;
  try change (10 + 15) with 25;
  try change (11 + 0)  with 11;
  try change (11 + 1)  with 12;
  try change (11 + 2)  with 13;
  try change (11 + 3)  with 14;
  try change (11 + 4)  with 15;
  try change (11 + 5)  with 16;
  try change (11 + 6)  with 17;
  try change (11 + 7)  with 18;
  try change (11 + 8)  with 19;
  try change (11 + 9)  with 20;
  try change (11 + 10) with 21;
  try change (11 + 11) with 22;
  try change (11 + 12) with 23;
  try change (11 + 13) with 24;
  try change (11 + 14) with 25;
  try change (11 + 15) with 26;
  try change (12 + 0)  with 12;
  try change (12 + 1)  with 13;
  try change (12 + 2)  with 14;
  try change (12 + 3)  with 15;
  try change (12 + 4)  with 16;
  try change (12 + 5)  with 17;
  try change (12 + 6)  with 18;
  try change (12 + 7)  with 19;
  try change (12 + 8)  with 20;
  try change (12 + 9)  with 21;
  try change (12 + 10) with 22;
  try change (12 + 11) with 23;
  try change (12 + 12) with 24;
  try change (12 + 13) with 25;
  try change (12 + 14) with 26;
  try change (12 + 15) with 27;
  try change (13 + 0)  with 13;
  try change (13 + 1)  with 14;
  try change (13 + 2)  with 15;
  try change (13 + 3)  with 16;
  try change (13 + 4)  with 17;
  try change (13 + 5)  with 18;
  try change (13 + 6)  with 19;
  try change (13 + 7)  with 20;
  try change (13 + 8)  with 21;
  try change (13 + 9)  with 22;
  try change (13 + 10) with 23;
  try change (13 + 11) with 24;
  try change (13 + 12) with 25;
  try change (13 + 13) with 26;
  try change (13 + 14) with 27;
  try change (13 + 15) with 28;
  try change (14 + 0)  with 14;
  try change (14 + 1)  with 15;
  try change (14 + 2)  with 16;
  try change (14 + 3)  with 17;
  try change (14 + 4)  with 18;
  try change (14 + 5)  with 19;
  try change (14 + 6)  with 20;
  try change (14 + 7)  with 21;
  try change (14 + 8)  with 22;
  try change (14 + 9)  with 23;
  try change (14 + 10) with 24;
  try change (14 + 11) with 25;
  try change (14 + 12) with 26;
  try change (14 + 13) with 27;
  try change (14 + 14) with 28;
  try change (14 + 15) with 29;
  try change (15 + 0)  with 15;
  try change (15 + 1)  with 16;
  try change (15 + 2)  with 17;
  try change (15 + 3)  with 18;
  try change (15 + 4)  with 19;
  try change (15 + 5)  with 20;
  try change (15 + 6)  with 21;
  try change (15 + 7)  with 22;
  try change (15 + 8)  with 23;
  try change (15 + 9)  with 24;
  try change (15 + 10) with 25;
  try change (15 + 11) with 26;
  try change (15 + 12) with 27;
  try change (15 + 13) with 28;
  try change (15 + 14) with 29;
  try change (15 + 15) with 30;
  try change (1 - 1)  with 0;
  try change (2 - 1)  with 1;
  try change (3 - 1)  with 2;
  try change (4 - 1)  with 3;
  try change (5 - 1)  with 4;
  try change (6 - 1)  with 5;
  try change (7 - 1)  with 6;
  try change (8 - 1)  with 7;
  try change (9 - 1)  with 8;
  try change (10 - 1) with 9;
  try change (11 - 1) with 10;
  try change (12 - 1) with 11;
  try change (13 - 1) with 12;
  try change (14 - 1) with 13;
  try change (15 - 1) with 14;
  try change (16 - 1) with 15. *)

Ltac change_Z_to_nat :=
  match goal with 
  |- context[Z.to_nat ?A] => 
      match is_Z A with
      | false => idtac
      | true  => let C := (eval compute in (Z.to_nat A)) in
        change (Z.to_nat A) with C
      end
   end.


(*
Ltac change_Z_to_nat :=
  try change (Z.to_nat 0) with 0%nat;
  try change (Z.to_nat 1) with 1%nat;
  try change (Z.to_nat 2) with 2%nat;
  try change (Z.to_nat 3) with 3%nat;
  try change (Z.to_nat 4) with 4%nat;
  try change (Z.to_nat 5) with 5%nat;
  try change (Z.to_nat 6) with 6%nat;
  try change (Z.to_nat 7) with 7%nat;
  try change (Z.to_nat 8) with 8%nat;
  try change (Z.to_nat 9) with 9%nat;
  try change (Z.to_nat 10) with 10%nat;
  try change (Z.to_nat 11) with 11%nat;
  try change (Z.to_nat 12) with 12%nat;
  try change (Z.to_nat 13) with 13%nat;
  try change (Z.to_nat 14) with 14%nat;
  try change (Z.to_nat 15) with 15%nat;
  try change (Z.to_nat 16) with 16%nat;
  try change (Z.to_nat 17) with 17%nat;
  try change (Z.to_nat 18) with 18%nat;
  try change (Z.to_nat 19) with 19%nat;
  try change (Z.to_nat 20) with 20%nat;
  try change (Z.to_nat 21) with 21%nat;
  try change (Z.to_nat 22) with 22%nat;
  try change (Z.to_nat 23) with 23%nat;
  try change (Z.to_nat 24) with 24%nat;
  try change (Z.to_nat 25) with 25%nat;
  try change (Z.to_nat 26) with 26%nat;
  try change (Z.to_nat 27) with 27%nat;
  try change (Z.to_nat 28) with 28%nat;
  try change (Z.to_nat 29) with 29%nat;
  try change (Z.to_nat 30) with 30%nat;
  try change (Z.to_nat 31) with 31%nat.
*)
Ltac gen_i H i :=
  assert(H: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7
    \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by omega
    ; repeat match goal with
      | [ H : ?i = _ \/ _ |- _ ] => destruct H ; try subst i
      end.
Close Scope Z.
