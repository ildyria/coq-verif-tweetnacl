(* From Tweetnacl.Libs Require Import Export.
From Tweetnacl.ListsOp Require Import Export.

From Tweetnacl.Gen Require Import AMZubSqSel.
From Tweetnacl.Gen Require Import ABCDEF.
From Tweetnacl.Low Require Import AMZubSqSel.
From Tweetnacl.Low Require Import ScalarMult_gen_small.
From Tweetnacl.Gen Require Import abstract_fn_rev.

Section ScalarRec.

Open Scope Z.

Context {O : Ops (list Z)}.
Context {ZO : Ops Z}.
Context {OP : @Ops_Prop O}.

Definition P x := ZofList 16 x.
Definition Mod x := Z.modulo x (Z.pow 2 255 - 19).

Variable A_eq : forall (a b:list Z), Mod (P (A a b)) = Mod (A (P a) (P b)).
Variable M_eq : forall (a b:list Z), Mod (P (M a b)) = Mod (M (P a) (P b)).
Variable Zub_eq : forall (a b:list Z),  Mod (P (Zub a b)) = Mod (Zub (P a) (P b)).
Variable Sq_eq : forall (a:list Z),  Mod (P (Sq a)) = Mod (Sq (P a)).
Variable _121665_eq : Mod (P _121665) = Mod (_121665).
Variable Sel25519_eq : forall b (p q:list Z),  Mod (P (Sel25519 b p q)) = Mod (Sel25519 b (P p) (P q)).
Variable getbit_eq : forall i (p:list Z),  getbit i p = getbit i (P p).

Variable Mod_ZSel25519_eq : forall b p q,  Mod (Sel25519 b p q) = Sel25519 b (Mod p) (Mod q).
Variable Mod_ZA_eq : forall p q,  Mod (A p q) = Mod (A (Mod p) (Mod q)).
Variable Mod_ZM_eq : forall p q,  Mod (M p q) = Mod (M (Mod p) (Mod q)).
Variable Mod_ZZub_eq : forall p q,  Mod (Zub p q) = Mod (Zub (Mod p) (Mod q)).
Variable Mod_ZSq_eq : forall p,  Mod (Sq p) = Mod (Sq (Mod p)).
Variable Mod_red : forall p,  Mod (Mod p) = (Mod p).

End ScalarRec.
 *)