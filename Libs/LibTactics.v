Require Export Libs.LibTactics_Rennes.

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

