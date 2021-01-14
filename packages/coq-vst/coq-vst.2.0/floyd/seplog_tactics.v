Require Import VST.floyd.base.
Require Import VST.floyd.val_lemmas.
Local Open Scope logic.

Hint Rewrite <- prop_and : gather_prop.

Lemma gather_prop_left {A}{NA: NatDed A}:
  forall P Q R,  !! P && (!! Q && R) = !!(P/\Q) && R.
Proof. intros. rewrite <- andp_assoc. rewrite <- prop_and; auto.
Qed.

Lemma gather_prop_right {A}{NA: NatDed A}:
  forall P Q R,  R && !! P && !! Q = !!(P/\Q) && R.
Proof. intros. rewrite andp_assoc. rewrite andp_comm.  rewrite <- prop_and; auto.
Qed.
Hint Rewrite gather_prop_left gather_prop_right : gather_prop.

Lemma andp_in_order1 {A}{NA: NatDed A}:
  forall P Q, P && Q = P && (P --> Q).
Proof.
  intros.
  apply pred_ext.
  + apply andp_derives; auto.
    apply imp_andp_adjoint.
    apply andp_left1; auto.
  + apply andp_right.
    - apply andp_left1; auto.
    - apply modus_ponens.
Qed.

Lemma andp_in_order2 {A}{NA: NatDed A}:
  forall P Q, P && Q = Q && (Q --> P).
Proof.
  intros.
  rewrite (andp_comm P Q).
  apply andp_in_order1.
Qed.

Lemma andp_right1{A}{NA: NatDed A}:
  forall P Q R, P |-- Q -> P && Q |-- R -> P |-- Q && R.
Proof.
  intros.
  rewrite andp_in_order1.
  apply andp_right; auto.
  apply imp_andp_adjoint; auto.
Qed.

Lemma andp_right2{A}{NA: NatDed A}:
  forall P Q R, P |-- R -> P && R |-- Q -> P |-- Q && R.
Proof.
  intros.
  rewrite andp_comm.
  apply andp_right1; auto.
Qed.

Definition not_a_prop {A} (P: A) := True.

Ltac not_a_prop := match goal with
  | |- not_a_prop  (prop _) => fail 1
  | |- _ => apply Coq.Init.Logic.I
end.

Lemma flip_prop {A}{NA: NatDed A}: forall P Q,
      not_a_prop P -> (P&& !! Q = !! Q && P).
Proof. intros. apply andp_comm. Qed.

Hint Rewrite @flip_prop using not_a_prop : gather_prop.

Lemma gather_prop3 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> R && (!! P && Q) = !!P && (R && Q).
Proof. intros. rewrite andp_comm. rewrite andp_assoc.
        rewrite (andp_comm Q); auto.
Qed.

Hint Rewrite @gather_prop3 using not_a_prop : gather_prop.

Lemma gather_prop4 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> (!!P && R) && Q = !!P && (R && Q).
Proof. intros. rewrite andp_assoc. auto.
Qed.
Hint Rewrite @gather_prop4 using not_a_prop : gather_prop.

Lemma gather_prop5 {A}{NA: NatDed A}:
  forall P Q R,  not_a_prop R -> not_a_prop Q -> (R && !!P && Q) = !!P && (R && Q).
Proof. intros. rewrite andp_assoc. rewrite andp_comm. rewrite andp_assoc.
  f_equal; apply andp_comm.
Qed.
Hint Rewrite @gather_prop5 using not_a_prop : gather_prop.

Hint Rewrite @sepcon_andp_prop @sepcon_andp_prop' : gather_prop.

(*Hint Rewrite <- sepcon_assoc : gather_prop.*)

Lemma go_lower_lem1:
  forall (P1 P: Prop) (QR PQR: mpred),
      (P1 -> prop P && QR |-- PQR) ->
      (prop (P1 /\ P ) && QR |-- PQR).
Proof.
 intros.
 apply derives_extract_prop; intros [? ?].
 apply derives_trans with (!!P && QR).
 apply andp_right; auto. apply prop_right; auto.
 apply H; auto.
Qed.

Lemma go_lower_lem1':
  forall (P1 P2 P: Prop) (QR PQR: mpred),
      (prop (P1 /\ (P2 /\ P)) && QR |-- PQR) ->
      (prop ((P1 /\ P2) /\ P ) && QR |-- PQR).
Proof.
 intros.
 eapply derives_trans;  [ | apply H].
 apply andp_derives; auto.
 apply prop_derives; intuition.
Qed.



(* These versions can sometimes take minutes,
   when A and B can't be unified
Hint Extern 1 (_ |-- _) => (simple apply (@derives_refl mpred _) ) : cancel.
Hint Extern 1 (_ |-- |> _) => (simple apply (@now_later mpred _ _) ) : cancel.
*)

Hint Extern 2 (?A |-- ?B) => (constr_eq A B; simple apply derives_refl) : cancel.
Hint Extern 2 (?A |-- |> ?B) => (constr_eq A B; simple apply now_later) : cancel.

Lemma cancel1_start:
 forall P Q : mpred,
   P |-- Q * emp ->
   P |-- Q.
Proof. Set Printing All. intros. rewrite sepcon_emp in H; auto.
Qed.

Lemma cancel1_here:
  forall P P' Q1 Q2 Q3 : mpred,
  P' |-- Q2 ->
  P |-- Q1 * Q3 ->
  P * P' |-- Q1 * Q2 * Q3.
Proof.
intros. rewrite (sepcon_comm Q1).
rewrite sepcon_assoc.  rewrite sepcon_comm. apply sepcon_derives; auto.
Qed.

Lemma cancel1_next:
  forall P Q1 Q2 Q3 : mpred,
   P |-- Q1 * (Q2 * Q3) ->
   P |-- Q1 * Q2 * Q3.
Proof. intros. rewrite sepcon_assoc; auto. Qed.

Lemma cancel1_last:
  forall P P' Q2 Q3 : mpred,
  P' |-- Q2 ->
  P |-- Q3 ->
  P * P' |-- Q2 * Q3.
Proof.
 intros. rewrite sepcon_comm; apply sepcon_derives; auto.
Qed.

Lemma cancel1_finish1:
  forall P Q1 Q2 Q3 : mpred,
   P |-- Q1 * Q2 * Q3 ->
   P |-- Q1 * (Q2 * Q3).
Proof.
 intros. rewrite <- sepcon_assoc. auto.
Qed.

Lemma cancel1_finish2:
  forall P Q : mpred,
    P |-- Q ->
   P |-- Q * emp.
Proof. intros. rewrite sepcon_emp; auto.
Qed.

Ltac cancel1 :=
 first [
   simple apply cancel1_here; [
    try match goal with H := _ : list mpred |- _ => clear H end; (*
      this line is to work around Coq 8.4 bug,
      Anomaly: undefined_evars_of_term *)
    solve [eauto with nocore cancel]
   | ]
 | simple apply cancel1_next; cancel1
 | simple apply cancel1_last; [
    try match goal with H := _ : list mpred |- _ => clear H end; (*
      this line is to work around Coq 8.4 bug,
      Anomaly: undefined_evars_of_term *)
    solve [eauto with nocore cancel] | ]
 ].

Ltac cancel2 :=
  simple apply cancel1_start;
  cancel1;
  repeat simple apply cancel1_finish1;
  try simple apply cancel1_finish2.

Ltac lift1 a e1 rho  :=
 match e1 with
 | lift0 rho => constr:(a)
 | lift0 ?a1 => constr: (lift0 (a a1))
 | _ => constr:(lift1 a e1)
 end.

Ltac lift2 a e1 e2 rho :=
 match e1 with
 |  lift0 ?a1 => lift1 (a a1) e2 rho
 | _ => constr:(lift2 a e1 e2)
 end.

Ltac lift3 a e1 e2 e3 rho :=
 match e1 with
 |  lift0 ?a1 => lift2 (a a1) e2 e3 rho
 | _ => constr:(lift3 a e1 e2 e3)
 end.

Ltac lift4 a e1 e2 e3 e4 rho :=
 match e1 with
 |  lift0 ?a1 => lift3 (a a1) e2 e3 e4 rho
 | _ => constr:(lift4 a e1 e2 e3 e4)
 end.

Ltac abstract_env rho P :=
  match P with
   | @emp mpred _ _ => constr:(@emp (environ->mpred) _ _)
   | @sepcon mpred _ _ ?e1 ?e2 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
       in constr:(@sepcon (environ->mpred) _ _ e1' e2')
   | ?a0 ?a1 ?a2 ?e1 ?e2 ?e3 ?e4 =>
      let e1' := abstract_env rho e1  in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1 a2) e1' e2' e3' e4' rho
   | ?a0 ?a1 ?e1 ?e2 ?e3 ?e4 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift3 (a0 a1) e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 ?e4 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3 in let e4' := abstract_env rho e4
      in lift4 a0 e1' e2' e3' e4' rho
   | ?a0 ?e1 ?e2 ?e3 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2 in let e3' := abstract_env rho e3
      in lift3 a0 e1' e2' e3' rho
   | ?a0 ?e1 ?e2 =>
      let e1' := abstract_env rho e1 in let e2' := abstract_env rho e2
      in lift2 a0 e1' e2' rho
   | ?a0 ?e1 => let e1' := abstract_env rho e1 in lift1 a0 e1' rho
   | rho => constr: (lift1)
   | ?a => constr:(lift0 a)
   end.

Lemma cancel_frame0{A}{ND: NatDed A}{SL: SepLog A}:
  forall rho: environ, emp rho |-- fold_right sepcon emp nil rho.
Proof. intro; apply derives_refl. Qed.

Lemma cancel_frame0_low:
  emp |-- fold_right_sepcon nil.
Proof.  apply derives_refl. Qed.

Lemma cancel_frame2: forall (P Q: environ->mpred) F (rho: environ),
     Q rho |-- 	fold_right sepcon emp F rho ->
    (P * Q) rho |-- fold_right sepcon emp (P::F) rho.
Proof. intros. simpl. apply sepcon_derives; auto.
Qed.

Lemma cancel_frame2_low: forall (P Q: mpred) F,
     Q  |-- fold_right_sepcon F  ->
    (P * Q) |-- fold_right_sepcon (P::F).
Proof. intros. apply sepcon_derives; auto.
Qed.

Lemma cancel_frame1: forall (P: environ->mpred) (rho: environ),
         P rho |-- fold_right sepcon emp (P::nil) rho.
Proof. intros. unfold fold_right. rewrite sepcon_emp; apply derives_refl.
Qed.

Lemma cancel_frame1_low: forall (P: mpred),
         P |-- fold_right_sepcon (P::nil).
Proof. intros. unfold fold_right_sepcon. rewrite sepcon_emp; apply derives_refl.
Qed.


Ltac fixup_lifts :=
 repeat
 match goal with
 | |- context[@lift0 mpred] => change (@lift0 mpred) with (@liftx (LiftEnviron mpred))
 | |- context[@lift1 ?A] => change (@lift1 A mpred) with (@liftx (Tarrow A (LiftEnviron mpred)))
 | |- context[@lift2 ?A ?B] =>  change (@lift2 A B mpred) with (@liftx (Tarrow A (Tarrow B (LiftEnviron mpred))))
 | |- context[@lift3 ?A ?B ?C] => change (@lift3 A B C mpred) with (@liftx (Tarrow A (Tarrow B (Tarrow C (LiftEnviron mpred)))))
 | |- context[@lift4 ?A ?B ?C ?D] => change (@lift4 A B C D mpred) with (@liftx (Tarrow A (Tarrow B (Tarrow C (Tarrow D (LiftEnviron mpred))))))
 end.

Fixpoint fold_right_sepconx (l: list mpred) : mpred :=
match l with
| nil => emp
| a::nil => a
| a::b => a * fold_right_sepconx b
end.

Lemma fold_right_sepconx_eq:
  forall l, fold_right_sepconx l = fold_right_sepcon l.
Proof.
induction l; simpl; auto.
rewrite IHl.
destruct l; simpl; auto. rewrite sepcon_emp; auto.
Qed.

Lemma fold_right_sepconx_eqx:
  forall A B, A |-- fold_right_sepconx B -> A |-- fold_right_sepcon B.
Proof.
intros.
rewrite <- fold_right_sepconx_eq; auto.
Qed.

Ltac unfold_right_sepcon A :=
 lazymatch A with
 | (?B * ?C)%logic => let x := unfold_right_sepcon C
                               in let y := constr:(B :: x)
                               in y
 | ?D => let y := constr:(D::nil) in y
end.

Ltac cancel_frame :=
match goal with
| |- _ |-- fold_right_sepcon _  => (* setup *)
   rewrite !sepcon_assoc; cancel_frame
| F := ?v |- ?A |-- fold_right_sepcon ?F  => (* fast way *)
   is_evar v;
   apply fold_right_sepconx_eqx;
   let w := unfold_right_sepcon A
    in instantiate (1:=w) in (Value of F);
    unfold F;
    unfold fold_right_sepconx;
    simple apply derives_refl
(*
| |- _ |-- fold_right_sepcon ?F  =>  (* slow way *)
   repeat apply cancel_frame2_low;
    try (unfold F; apply cancel_frame0_low);
    try (unfold F; apply cancel_frame1_low)
*)
| |- ?P |-- fold_right _ _ ?F ?rho  =>
     let P' := abstract_env rho P in
       change ( P' rho |-- fold_right sepcon emp F rho);
   fixup_lifts; cbv beta;
    repeat rewrite sepcon_assoc;
   repeat match goal with |- (_ * _) _ |-- _ =>
                   apply cancel_frame2
                    end;
    try (unfold F; apply cancel_frame1);
    try (instantiate (1:=nil) in (Value of F); unfold F; apply cancel_frame0)
 end.


Ltac pull_left A :=
 (* For some reason in Coq 8.4pl3 and perhaps other versions,
  this works better than the version in log_normalize
  which is simply,
   repeat rewrite <- (pull_right A) || rewrite <- (pull_right0 A)
  and which sometimes fails when the terms get complicated.
 *)
  repeat match goal with
  | |- context [?Q * ?R * A] => rewrite <- (pull_right A Q R)
  | |- context [?Q * A] => rewrite <- (pull_right0 A Q)
  end.

Lemma cancel_left: forall P Q R: mpred,
   Q |-- R -> P * Q |-- P * R.
Proof.
intros; apply sepcon_derives; auto.
Qed.

Lemma pull_left_special: forall A B C : mpred,
    (B * (A * C)) = (A * (B * C)).
Proof.
intros. rewrite sepcon_comm. rewrite sepcon_assoc. f_equal.
 apply sepcon_comm.
Qed.

Lemma pull_left_special0: forall A B : mpred,
    (B * A) = (A * B).
Proof.
intros; apply sepcon_comm.
Qed.

Ltac qcancel P :=
 lazymatch P with
 | sepcon ?A ?B => 
     match goal with |- _ |-- ?Q =>
       try match Q with context [A] =>
        let a := fresh "A" in set (a:=A);
         rewrite ?(pull_left_special0 a), ?(pull_left_special a);
         apply cancel_left;
         clear a
       end;
       qcancel B
     end
 | ?A => 
     try match goal with |- _ |-- ?Q =>
       lazymatch Q with context [A] =>
        let a := fresh "A" in set (a:=A);
         rewrite ?(pull_left_special0 a), ?(pull_left_special a);
         rewrite ?(pull_left_special0 A), ?(pull_left_special A);
         apply cancel_left;
         clear a
      end
     end
 end.

Ltac cancel :=
  rewrite ?sepcon_assoc;
  repeat match goal with |- ?A * _ |-- ?B * _ => 
     constr_eq A B;  simple apply (cancel_left A)
  end;
  match goal with |- ?P |-- _ => qcancel P end;
  repeat first [rewrite emp_sepcon | rewrite sepcon_emp];
  try match goal with |- ?A |-- ?B => 
       constr_eq A B; simple apply (derives_refl A)
  end;
  match goal with |- ?P |-- _ =>
   (* The "emp" is a marker to notice when one complete pass has been made *)
   rewrite <- (emp_sepcon P)
  end;
  repeat rewrite <- sepcon_assoc;
  repeat match goal with
    | |- sepcon _ emp |-- _ => fail 1
    | |- sepcon _ TT |-- _ => pull_left (@TT mpred _)
    | |- sepcon _ ?P' |-- _ => first [ cancel2 | pull_left P' ]
   end;
  repeat first [rewrite emp_sepcon | rewrite sepcon_emp];
  pull_left (@TT mpred _);
  first [ simple apply derives_refl'; repeat f_equal; reflexivity (* this is NOT a _complete_ tactic;
                 for example, "simple apply derives_refl" would be more complete.  But that
                 tactic can sometimes take minutes to discover that something doesn't unify;
                 what I have here is a compromise between reliable speed, and (in)completeness.
               *)
          | apply TT_right
          | apply sepcon_TT
          | apply TT_sepcon
          | cancel_frame
          | idtac
          ].

Ltac apply_find_core X :=
 match X with
 | ?U -> ?V => match type of U with Prop => apply_find_core V end
 | @derives mpred _ _ _ => constr:(X)
 end.

Ltac sep_apply_with_tac H tac :=
  match goal with |- ?A |-- ?B =>
    match type of H with ?TH =>
      match apply_find_core TH with  ?C |-- ?D =>
        let frame := fresh "frame" in evar (frame: list mpred);
        apply derives_trans with (C * fold_right_sepcon frame);
        [ pattern C;
          let FF := fresh "F" in
          match goal with | |- ?F C => set (FF := F) end;
          tac; subst FF; cbv beta;
          solve [cancel] 
        | eapply derives_trans; 
          [ apply sepcon_derives; [clear frame; apply H | apply derives_refl] 
          | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp
          ]
        ]
     end
    end
  end.

Ltac sep_apply_without_tac H :=
    match goal with |- ?A |-- ?B =>
     match type of H with ?TH =>
     match apply_find_core TH with  ?C |-- ?D =>
      let frame := fresh "frame" in evar (frame: list mpred);
       apply derives_trans with (C * fold_right_sepcon frame);
             [solve [cancel] 
             | eapply derives_trans; 
                 [apply sepcon_derives; [clear frame; apply H | apply derives_refl] 
                 | subst frame; unfold fold_right_sepcon; rewrite ?sepcon_emp
                 ]
             ]
     end
     end
    end.

Tactic Notation "sep_apply" constr(H) "using" tactic(tac) :=
  sep_apply_with_tac H tac.

Tactic Notation "sep_apply" constr(H) :=
  sep_apply_without_tac H.

Lemma wand_refl_cancel_right:
  forall {A}{ND: NatDed A} {SL: SepLog A}{CA: ClassicalSep A}
    (P: A),  emp |-- P -* P.
Proof.
intros. apply wand_sepcon_adjoint.
rewrite emp_sepcon. apply derives_refl.
Qed.

Lemma cancel_emp_wand:
  forall P Q R: mpred,
    P |-- Q ->
    P |-- Q * (R -* R).
Proof.
intros. rewrite <- (sepcon_emp P).
apply sepcon_derives; auto.
apply wand_refl_cancel_right.
Qed.

Ltac cancel_wand :=
  repeat
  match goal with |- _ |-- ?B =>
    match B with context [?A -* ?A] =>
    rewrite ?sepcon_assoc;
    pull_right (A -* A);
    first [apply cancel_emp_wand | apply wand_refl_cancel_right]
    end
  end.

Ltac norm_rewrite := autorewrite with norm.
 (* New version: rewrite_strat (topdown hints norm).
     But this will have to wait for a future version of Coq
    in which rewrite_strat discharges side conditions.
    According to Matthieu Sozeau, in the Coq trunk as of June 5, 2013,
    rewrite_strat is documented AND discharges side conditions.
    It might be about twice as fast, or 1.7 times as fast, as the old autorewrite.
    And then, maybe use "bottomup" instead of "topdown", see if that's better.

   To test whether your version of Coq works, use this:
Lemma L : forall n, n=n -> n + 1 = S n.
Proof. intros. rewrite <- plus_n_Sm ,<- plus_n_O. reflexivity.
Qed.
Hint Rewrite L using reflexivity : test888.
Goal forall n, S n = n + 1.
intros.
rewrite_strat (topdown hints test888).
match goal with |- S n = S n => reflexivity end.
(* should be no extra (n=n) goal here *)
Qed.
 *)

Ltac normalize1 :=
         match goal with
            | |- context [@andp ?A (@LiftNatDed ?T ?B ?C) ?D ?E ?F] =>
                      change (@andp A (@LiftNatDed T B C) D E F) with (D F && E F)
            | |- context [@later ?A  (@LiftNatDed ?T ?B ?C) (@LiftIndir ?X1 ?X2 ?X3 ?X4 ?X5) ?D ?F] =>
                   change (@later A  (@LiftNatDed T B C) (@LiftIndir X1 X2 X3 X4 X5) D F)
                     with (@later B C X5 (D F))
            | |- context [@sepcon ?A (@LiftNatDed ?B ?C ?D)
                                                         (@LiftSepLog ?E ?F ?G ?H) ?J ?K ?L] =>
                   change (@sepcon A (@LiftNatDed B C D) (@LiftSepLog E F G H) J K L)
                      with (@sepcon C D H (J L) (K L))
            | |- context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) by (auto with norm)
            | |- context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) by (auto with norm)
            | |- context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) by (auto with norm)
            | |- context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) by (auto with norm)
            | |-  derives ?A   ?B => match A with
                   | FF => apply FF_left
                   | !! _ => apply derives_extract_prop0
                   | exp (fun y => _) => apply imp_extract_exp_left; (intro y || intro)
                   | !! _ && _ => apply derives_extract_prop
                   | _ && !! _ => apply derives_extract_prop'
                   | context [ ((!! ?P) && ?Q) && ?R ] => rewrite (andp_assoc (!!P) Q R)
                   | context [ ?Q && (!! ?P && ?R)] =>
                                  match Q with !! _ => fail 2 | _ => rewrite (andp_assoc' (!!P) Q R) end
                 (* In the next four rules, doing it this way (instead of leaving it to autorewrite)
                    preserves the name of the "y" variable *)
                   | context [andp (exp (fun y => _)) _] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [andp _ (exp (fun y => _))] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [sepcon (exp (fun y => _)) _] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                               apply imp_extract_exp_left; intro y
                   | context [sepcon _ (exp (fun y => _))] =>
                               let BB := fresh "BB" in set (BB:=B); norm_rewrite; unfold BB; clear BB;
                                apply imp_extract_exp_left; intro y
                   | _ => simple apply TT_prop_right
                   | _ => simple apply TT_right
                   | _ => apply derives_refl
                   end
              | |- _ => solve [auto]
              | |- _ |-- !! (?x = ?y) && _ =>
                            (rewrite (prop_true_andp' (x=y))
                                            by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (rewrite (prop_true_andp' (x=y))
                                            by (unfold x; reflexivity); unfold x in *; clear x)
              |  |- ?ZZ -> ?YY => match type of ZZ with
                                               | Prop => fancy_intros true || fail 1
                                               | _ => intros _
                                              end
              | |- ~ _ => fancy_intro true
              | |- _ => progress (norm_rewrite) (*; auto with typeclass_instances *)
              | |- forall _, _ => let x := fresh "x" in (intro x; repeat normalize1; try generalize dependent x)
              end.

Ltac normalize :=
   autorewrite with gather_prop;
   repeat (((repeat simple apply go_lower_lem1'; simple apply go_lower_lem1)
              || simple apply derives_extract_prop
              || simple apply derives_extract_prop');
              fancy_intros true);
   repeat normalize1; try contradiction.
