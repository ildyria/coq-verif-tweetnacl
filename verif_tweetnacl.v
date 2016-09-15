Require Import floyd.proofauto. (* Import the Verifiable C system *)
Require Import tweetnacl. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import arith.



(* Beginning of the API spec for the sumarray.c program *)
Definition A_spec n :=
 DECLARE _A
  WITH i: val, o: val, a: val, b: val, sh : share, contents_o : list Z, contents_a : list Z, contents_b : list Z
  PRE [ _o OF (tptr tlong), _a OF (tptr tlong), _b OF (tptr tlong) ]
        PROP  (readable_share sh;
                Forall (fun x => 0 <= x <= Z.pow 2 n) contents_a;
                Forall (fun x => 0 <= x <= Z.pow 2 n) contents_b)
        LOCAL (temp _i i)
        SEP   (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_o)) o)
  POST [ tvoid ]
        PROP (readable_share sh;
                Forall (fun x => 0 <= x <= Z.pow 2 (Z.succ n)) contents_o)
        LOCAL()
        SEP (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b;
              data_at sh (tarray tlong 16) (map Vlong (map Int64.repr (sum_list_Z contents_a contents_b))) o).

(* Note: It would also be reasonable to let [contents] have type [list int].
  Then the [Forall] would not be needed in the PROP part of PRE.
*)

Definition A_Inv sh a b contents_a contents_b := 
   PROP  ()
   LOCAL ()
   SEP   (data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_a)) a;
          data_at sh (tarray tlong 16) (map Vlong (map Int64.repr contents_b)) b).


(* Packaging the API spec all together. *)
Definition Gprog n  : funspecs := 
      augment_funspecs prog [A_spec n].

(** Proof that f_sumarray, the body of the sumarray() function,
 ** satisfies sumarray_spec, in the global context (Vprog,Gprog).
 **)
Lemma body_sumarray n: semax_body Vprog (Gprog n) f_A (A_spec n).
Proof.
start_function.
forward.