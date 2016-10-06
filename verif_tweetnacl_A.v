Require Import floyd.proofauto. (* Import the Verifiable C system *)

Require Import tweetnacl. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import SumList.
Require Import ToFF.

Open Scope Z.

Lemma SumListForall : forall n a b c,
  n > 0 ->
  Forall (fun x : Z => 0 <= x < 2 ^ n) a ->
  Forall (fun x : Z => 0 <= x < 2 ^ n) b ->
  sum_list_Z a b = c ->
  Forall (fun x : Z => 0 <= x < 2 ^ (Z.succ n)) c.
Proof.
induction n ; [intros | | intros; assert(Hp:=Zlt_neg_0)] ; go.
assert(Hp: exists n, n = Z.pos p) by (exists (Z.pos p); reflexivity); destruct Hp as [n Hp].
rewrite <- Hp in *.
assert(Hfa: forall a, 0 <= a < 2^n -> 0 <= a < 2^Z.succ n).
intros x Hx ; split ; destruct Hx ; auto ; rewrite Z.pow_succ_r ; assert(Hpp:= Zgt_pos_0 p) ; rewrite <- Hp in Hpp ; omega.
induction a,b ; intros c Hn Ha Hb Hsum ; simpl in Hsum ; subst c ; auto.
- eapply (Forall_impl (fun x : Z => 0 <= x < 2 ^ Z.succ n) Hfa) ; auto.
- eapply (Forall_impl (fun x : Z => 0 <= x < 2 ^ Z.succ n) Hfa) ; auto.
  apply Forall_cons.
  {
  inv Ha.
  inv Hb.
  destruct H1.
  destruct H3.
  split ; try omega.
  apply addition ; try omega.
  }
  {
  apply (IHa b); auto.
  inv Ha ; auto.
  inv Hb ; auto.
  }
Qed.



(* Beginning of the API spec for the sumarray.c program *)
Definition A_spec :=
 DECLARE _A
  WITH i: val, o: val, a: val, b: val, aux1: val, aux2: val, sh : share, contents_o : list Z, contents_a : list Z, contents_b : list Z
  PRE [ _o OF (tptr tlong), _a OF (tptr tlong), _b OF (tptr tlong) ]
        PROP  (writable_share sh;
                Forall (fun x => 0 <= x < Z.pow 2 63) contents_a;
                Forall (fun x => 0 <= x < Z.pow 2 63) contents_b;
                length contents_a = 16%nat;
                length contents_b = 16%nat;
                length contents_o = 16%nat)
        LOCAL (temp _i i; temp _aux1 aux1; temp _aux2 aux2)
        SEP   (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_o)) o)
  POST [ tvoid ]
        PROP (writable_share sh;
                Forall (fun x => 0 <= x < Z.pow 2 (Z.succ 63)) contents_o)
        LOCAL()
        SEP (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr (sum_list_Z contents_a contents_b))) o).

(* Note: It would also be reasonable to let [contents] have type [list int].
  Then the [Forall] would not be needed in the PROP part of PRE.
*)
Check temp.

Definition A_Inv sh o a b contents_o contents_a contents_b aux1 aux2:= 
  EX i : Z,
   PROP  (writable_share sh;
          Forall (fun x => 0 <= x < Z.pow 2 63) contents_a;
          Forall (fun x => 0 <= x < Z.pow 2 63) contents_b;
          length contents_a = 16%nat;
          length contents_b = 16%nat;
          length contents_o = 16%nat;
          i >= 0;
          sum_list_Z_n (nat_of_Z i) contents_a contents_b = slice (nat_of_Z i) contents_o)
   LOCAL (temp _aux1 aux1; temp _aux2 aux2)
   SEP   (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr (sum_list_Z_n (nat_of_Z i) contents_a contents_b ++ tail (nat_of_Z i) contents_o))) o;
          data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
          data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b).


(* Packaging the API spec all together. *)
Definition Gprog : funspecs := 
      augment_funspecs prog [A_spec].


(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray: semax_body Vprog Gprog f_A A_spec.
Proof.
start_function.
forward_for_simple_bound 16 (A_Inv sh o a b contents_o contents_a contents_b aux1 aux2).
- go_lowerx.
  entailer!.
  flatten.
  flatten ; entailer!.
- go_lowerx.
  normalize.
  entailer!.
  unfold tc_expr.
  unfold "`" in *.
  simpl in *.
  entailer!.
- normalize.
  forward. (* ??? *)

- normalize.
  rewrite <- sum_list_eq in H5 ; go.
  rewrite slice_length_eq in H5 ; go.
  rewrite tail_length_eq ; go.
  rewrite app_nill_r.
  change (nat_of_Z 16) with (16%nat) in *.
  rewrite <- sum_list_eq ; go.
  assert(HSum:= SumListForall 63 contents_a contents_b (sum_list_Z contents_a contents_b)).
  assert(HSum': 63 > 0) by omega.
  apply HSum in HSum' ; go.
  normalize.
  rewrite H5 in HSum'.
  entailer!.
  forward.
Admitted.
