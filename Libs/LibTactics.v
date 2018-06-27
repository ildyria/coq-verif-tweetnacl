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
      | true  => let C := (eval compute in (Z.sub A B)) in
        change (Z.sub A B) with C
      end
    end
  end.

Ltac Grind_add_Z := Grind_add_Z_ ; Grind_sub_Z_.

Ltac change_Z_to_nat :=
  match goal with
  |- context[Z.to_nat ?A] => 
      match is_Z A with
      | false => idtac
      | true  => let C := (eval compute in (Z.to_nat A)) in
        change (Z.to_nat A) with C
      end
  | _ => idtac
  end.

Ltac is_nat n := match n with
  | 0%nat => true
  | (S _)%nat => true
  | _ => false
  end.

Ltac change_Z_of_nat :=
  match goal with
  |- context[Z.of_nat ?A] => 
      match is_nat A with
      | false => idtac
      | true  => let C := (eval compute in (Z.of_nat A)) in
        change (Z.of_nat A) with C
      end
  | _ => idtac
  end.

Ltac gen_hyp i nmax dec := 
    let n := (eval compute in (nmax - dec)) in
    match dec with
    | 0 => constr:(i = n)
    | dec =>
      let ndec := (eval compute in (dec - 1)) in 
      let tail_rec := gen_hyp i nmax ndec in
      constr:(i = n \/ tail_rec)
    end.

Ltac assert_gen_hyp i nmax dec :=
  let v := gen_hyp i nmax dec in 
  assert(v).

Ltac assert_gen_hyp_ H i nmax dec :=
  let v := gen_hyp i nmax dec in 
  assert(H : v).

Ltac gen_i H i :=
  assert_gen_hyp_ H i 15 15; [omega|];
(* assert(H: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7
    \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by omega; *)
  repeat match goal with
    | [ H : ?i = _ \/ _ |- _ ] => destruct H ; try subst i
  end.

(* I would like something like that... *)
(* Ltac nat_indify i :=
  match goal with
    | [ |- ?A ] => let A' := constr:(fun (i:Z) => A) in eapply (natlike_ind A')
  end.
just do:
pattern 1.
eapply natlike_ind.
*)

Ltac revert_all :=
  repeat match goal with
    | [ H : _ |- _ ] => revert H
  end.

Close Scope Z.
