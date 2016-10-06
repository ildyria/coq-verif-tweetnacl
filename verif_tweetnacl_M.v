Require Import floyd.proofauto. (* Import the Verifiable C system *)

Require Import tweetnacl. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import M.


Definition M_spec :=
 DECLARE _M
  WITH i: val, o: val, a: val, b: val, aux1: val, aux2: val, sh : share, contents_o : list Z, contents_a : list Z, contents_b : list Z
  PRE [ _o OF (tptr tlong), _a OF (tptr tlong), _b OF (tptr tlong) ]
        PROP  (readable_share sh;
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
        PROP (readable_share sh;
                Forall (fun x => 0 <= x < Z.pow 2 (Z.succ 63)) contents_o)
        LOCAL()
        SEP (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr (sum_list_Z contents_a contents_b))) o).

(* Packaging the API spec all together. *)
Definition Gprog : funspecs := 
      augment_funspecs prog [M_spec].


(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray: semax_body Vprog Gprog f_M M_spec.
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
  admit.
- admit.
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

Qed.
