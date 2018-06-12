From Tweetnacl.Libs Require Import Export.
From Tweetnacl.Gen Require Export AMZubSqSel.
From Tweetnacl.Gen Require Export AMZubSqSel_List.

Open Scope Z.

Inductive Z_List_Bound_es := 
  LB (l:list Z) n vmin vmax:
    Zlength l = n ->
    Forall (fun x => vmin <= x < vmax) l ->
    Z_List_Bound_es.

Inductive List16 (T:Type) :=
  Len (l:list T):
    Zlength l = 16 ->
    List16 T.
Arguments Len [T].

Definition List16_to_List {T: Type} (l: List16 T) : list T :=  match l with
  | Len l _ => l
end.

Lemma List16_Zlength : forall {T: Type} (l : List16 T),
  Zlength (List16_to_List l) = 16.
Proof. intros; destruct l ; simpl ; assumption. Qed.

Inductive List32B :=
  L32B (l:list Z):
    Forall (fun x => 0 <= x < 2^8) l ->
    List32B.

Definition List32_to_List (l: List32B) : list Z :=  match l with
  | L32B l _ => l
end.

Lemma List32B_bound : forall (l : List32B),
  Forall (fun x => 0 <= x < 2^8) (List32_to_List l).
Proof. intros; destruct l ; simpl ; assumption. Qed.


Section List16.

Context {OLZ : Ops (list Z) (list Z) id}.
Context {OPLZ : @Ops_List OLZ}.

Definition A_List16 (a b: List16 Z) := match a,b with
  | Len a Ha, Len b Hb => Len (A a b) (A_Zlength a b Ha Hb)
end.
Definition M_List16 (a b: List16 Z) := match a,b with
  | Len a Ha, Len b Hb => Len (M a b) (M_Zlength a b Ha Hb)
end.
Definition Zub_List16 (a b: List16 Z) := match a,b with
  | Len a Ha, Len b Hb => Len (Zub a b) (Zub_Zlength a b Ha Hb)
end.
Definition Sq_List16 (a: List16 Z) := match a with
  | Len a Ha => Len (Sq a) (Sq_Zlength a Ha)
end.
Definition Sel25519_List16 b (p q: List16 Z) := match p,q with
  | Len p Hp, Len q Hq => Len (Sel25519 b p q) (Sel25519_Zlength b p q Hp Hq)
end.
Definition C_121665_List16 := Len (C_121665) (C_121665_Zlength).

Definition C_1_List16 := Len (C_1) (C_1_Zlength).

Definition C_0_List16 := Len (C_0) (C_0_Zlength).

Definition getbit_List32B n (l: List32B) := match l with
  | L32B l _ => Getbit n l
end.

Local Instance List16_Ops : (Ops (@List16 Z) List32B id) := {}.
Proof.
apply A_List16.
apply M_List16.
apply Zub_List16.
apply Sq_List16.
apply C_0_List16.
apply C_1_List16.
apply C_121665_List16.
apply Sel25519_List16.
apply getbit_List32B.
apply id.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
simpl ; reflexivity.
Defined.

End List16.

Close Scope Z.