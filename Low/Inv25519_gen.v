Require Import Tweetnacl.Libs.Export.
Require Import Recdef.
(*
Require Import Tweetnacl.Libs.HeadTailRec.
*)

Section ScalarRec.
Open Scope Z.

Variable M : list Z -> list Z -> list Z.
Variable Sq : list Z -> list Z.

(*
sv inv25519(gf o,const gf i)
{
  gf c;
  int a;
  FOR(a,16) c[a]=i[a];
  for(a=253;a>=0;a--) {
    S(c,c);
    if(a!=2&&a!=4) M(c,c,i);
  }
  FOR(a,16) o[a]=c[a];
}
*)

Definition recurse (a : Z) : nat := Z.to_nat (a + 1).

Definition step_pow (a:Z) (c g:list Z) : list Z :=
    let c := Sq c in
      if (andb (Zneq_bool a 1) (Zneq_bool a 3))
      then M c g
      else c.

Function pow_fn_rev (a b:Z) (c g: list Z) {measure Z.to_nat a} : (list Z) :=
  if (a <=? 0)
    then c
    else
      let prev := pow_fn_rev (a - 1) b c g in 
        step_pow (b - 1 - a) prev g.
Proof. intros. apply Z2Nat.inj_lt ; move: teq ; rewrite Z.leb_gt => teq; omega. Defined.

Lemma pow_fn_rev_0 : forall b c g,
  pow_fn_rev 0 b c g = c.
Proof. go. Qed.

Lemma pow_fn_rev_n : forall a b c g,
  0 < a ->
  pow_fn_rev a b c g = step_pow (b - 1 - a) (pow_fn_rev (a - 1) b c g) g.
Proof. intros. rewrite pow_fn_rev_equation.
flatten ; apply Zle_bool_imp_le in Eq; omega.
Qed.

Variable M_Zlength : forall a b, Zlength a = 16 -> Zlength b = 16 -> Zlength (M a b) = 16.
Variable Sq_Zlength : forall a, Zlength a = 16 -> Zlength (Sq a) = 16.

Lemma step_pow_Zlength : forall a c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Zlength (step_pow a c g) = 16.
Proof.
  intros.
  rewrite /step_pow.
  flatten;
  repeat match goal with
     | _ => auto
     | _ => rewrite M_Zlength
     | _ => rewrite Sq_Zlength
   end.
Qed.

Lemma pow_fn_rev_Zlength : forall a b c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Zlength (pow_fn_rev a b c g) = 16.
Proof.
destruct a; intros.
go.
2: go.
remember (Z.pos p) as a.
assert(0 <= a).
  subst; apply Zle_0_pos.
clears p.
gen b c g.
gen a.
apply (natlike_ind (fun a => forall (b : ℤ) (c : list ℤ),
Zlength c = 16 -> forall g : list ℤ, Zlength g = 16 -> Zlength (pow_fn_rev a b c g) = 16)).
intros; go.
intros a Ha IHa b c Hc g Hg .
rewrite pow_fn_rev_equation.
flatten.
oreplace (Z.succ a- 1) a.
apply step_pow_Zlength ; auto.
Qed.

Variable M_bound_Zlength : forall a b,
  Zlength a = 16 ->
  Zlength b = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) b ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (M a b).
Variable Sq_bound_Zlength : forall a,
  Zlength a = 16 ->
  Forall (fun x => -Z.pow 2 26 < x < Z.pow 2 26) a ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (Sq a).

Local Ltac solve_Zlength :=
  intros;
  repeat match goal with
    | _ => orewrite M_Zlength
    | _ => orewrite Sq_Zlength
  end ; auto.

Local Ltac Simplify_this :=
change (2^16) with 65536 in *;
change (2^26) with 67108864 in *.

Lemma step_pow_bound_Zlength : forall a c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) g ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (step_pow a c g).
Proof.
  intros.
  rewrite /step_pow.
  flatten;
  repeat match goal with
    | _ => Simplify_this ; intros x Hx ; simpl in Hx ; omega
    | _ => apply M_bound_Zlength ; solve_Zlength
    | _ => apply Sq_bound_Zlength ; solve_Zlength
    | _ => apply H1
    | _ => apply H2
    | _ => eapply list.Forall_impl
  end.
Qed.

Lemma pow_fn_rev_bound_Zlength : forall a b c g,
  Zlength c = 16 ->
  Zlength g = 16 ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) c ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) g ->
  Forall (fun x => -38 <= x < Z.pow 2 16 + 38) (pow_fn_rev a b c g).
Proof.
destruct a; intros.
go.
2: go.
remember (Z.pos p) as a.
assert(0 <= a).
  subst; apply Zle_0_pos.
clears p.
gen b c g.
gen a.
apply (natlike_ind (fun a => 
forall (b : ℤ) (c : list ℤ),
Zlength c = 16 ->
Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) c ->
forall g : list ℤ,
Zlength g = 16 ->
Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) g -> Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) (pow_fn_rev a b c g))).
intros; go.
intros a Ha IHa b c Hc Hcc g Hg Hgg.
rewrite pow_fn_rev_equation.
flatten.
oreplace (Z.succ a- 1) a.
apply step_pow_bound_Zlength ; auto.
apply pow_fn_rev_Zlength ; auto.
Qed.

Close Scope Z.
End ScalarRec.