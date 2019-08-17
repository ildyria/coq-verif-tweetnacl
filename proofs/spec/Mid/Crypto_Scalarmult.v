From Tweetnacl Require Import Libs.Export.
From Tweetnacl Require Import Gen.Get_abcdef.
From Tweetnacl Require Import Gen.AMZubSqSel.
From Tweetnacl Require Import Gen.AMZubSqSel_Prop.
From Tweetnacl Require Import Gen.abstract_fn_rev.
From Tweetnacl Require Import Gen.montgomery_rec.
From Tweetnacl Require Import Gen.montgomery_rec_eq.
From Tweetnacl Require Import Mid.AMZubSqSel.
From Tweetnacl Require Import Mid.Reduce.
From Tweetnacl Require Import Mid.GetBit.
From Tweetnacl Require Import Mid.GetBit_bitn.
From Tweetnacl Require Import Mid.Prep_n.
From Tweetnacl Require Import Mid.Unpack25519.
From Tweetnacl Require Import Mid.Pack25519.
From Tweetnacl Require Import Mid.Car25519.
From Tweetnacl Require Import Mid.Inv25519.
From Tweetnacl Require Import Mid.Crypto_Scalarmult_Fp.
From Tweetnacl Require Import Mid.Crypto_Scalarmult_Mod.

From Tweetnacl.High Require Import Zmodp opt_ladder curve25519_Fp.
From mathcomp Require Import ssreflect eqtype ssralg.

From Tweetnacl Require Import Mod.
From Tweetnacl Require Import fermat.
From Tweetnacl Require Import Instances.
Open Scope Z.

Section ZCrypto_Scalarmult_gen.

Context (Z_Ops : (Ops Z Z) modP).

Definition ZCrypto_Scalarmult_rev_gen n p :=
  let t := abstract_fn_rev 255 254 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

End ZCrypto_Scalarmult_gen.

Definition ZCrypto_Scalarmult n p :=
  let t := montgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p) in
  ZPack25519 (Z.mul (get_a t) (ZInv25519 (get_c t))).

(* This is the equivalence between ladders defined as fn with type class and ladders defined as recursive *)
Theorem ZCrypto_Scalarmult_eq : forall (n p : Z),
  ZCrypto_Scalarmult n p = ZCrypto_Scalarmult_rev_gen Z_Ops n p.
Proof.
  intros.
  rewrite /ZCrypto_Scalarmult /ZCrypto_Scalarmult_rev_gen.
  replace (montgomery_rec 255 (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)) with
  (montgomery_rec (S (Z.to_nat 254)) (Zclamp n) 1 (ZUnpack25519 p) 0 1 0 0 (ZUnpack25519 p)).
  2: change (S (Z.to_nat 254)) with 255%nat.
  2: reflexivity.
  rewrite montgomery_rec_eq_fn_rev.
  2: omega.
  change (254 + 1) with 255.
  reflexivity.
Qed.

Lemma ZCrypto_Scalarmult_curve25519_ladder_ n x :
  ZCrypto_Scalarmult n x = val (curve25519_Fp_ladder (Z.to_nat (Zclamp n)) (Zmodp.pi (modP (ZUnpack25519 x)))).
Proof.
assert (Hn:= Zclamp_min n).
rewrite /ZCrypto_Scalarmult.
remember (Zclamp n) as N.
remember (ZUnpack25519 x) as X.
clear HeqX HeqN.
rewrite -Fp_Crypto_Scalarmult_rec_gen_equiv.
rewrite /ZPack25519.
rewrite /ZInv25519.
rewrite Zmult_mod.
rewrite pow_mod.
2: by compute.
rewrite /Fp_Crypto_Scalarmult_rec_gen.
rewrite /val /Zmodp_subType.
rewrite -modZp /p -lock.
remember (get_a
     (montgomery_rec 255 (Z.to_nat (N)) Zmodp.one (Zmodp.pi (modP (X))) Zmodp.zero Zmodp.one Zmodp.zero
        Zmodp.zero (Zmodp.pi (modP (X))))) as GETA.
remember (get_c
     (montgomery_rec 255 (Z.to_nat (N)) Zmodp.one (Zmodp.pi (modP (X))) Zmodp.zero Zmodp.one Zmodp.zero
        Zmodp.zero (Zmodp.pi (modP (X))))) as GETC.
assert(Mequiv:= M_eq GETA (GETC ^-1)).
cbn in Mequiv.
remember (Zmodp.repr (GETA / GETC)%R :𝓖𝓕) as HM.
cbn in HeqHM.
rewrite /modP in Mequiv.
Opaque montgomery_rec.
rewrite Mequiv in HeqHM.
rewrite /Mid.M in HeqHM.
do 2 rewrite -Zcar25519_correct in HeqHM.
clear Mequiv.
rewrite Zmult_mod in HeqHM.
rewrite HeqHM.
assert(H255: 0 <= 254 + 1).
  by compute.
assert(Hnn: ℤ.ℕ Z.to_nat N = N).
  rewrite Z2Nat.id //.
assert(Hxxx: val (Zmodp.pi (modP X)) = (modP X)).
  simpl. rewrite /modP /p -lock Z.mod_mod //=.
f_equal.
f_equal.
- {
  subst.
  change 255%nat with (S (Z.to_nat 254)).
  rewrite ?montgomery_rec_eq_fn_rev.
  2,3: done.
  assert(Habstr:= abstract_fn_rev_eq_a_Fp (254 + 1) 254 (Z.to_nat N) (Zmodp.pi (modP X)) N (modP X) H255 Hxxx Hnn).
  Opaque abstract_fn_rev.
  rewrite /P in Habstr.
  rewrite /Z25519_Z_Eq in Habstr.
  rewrite /val in Habstr.
  rewrite /Zmodp_subType in Habstr.
  symmetry.
  move: Habstr.
  rewrite {1}/modP => ->.
  assert(Habstr:= abstract_fn_rev_eq_a_Zmod (254 + 1) 254 N X H255).
  symmetry.
  move: Habstr.
  rewrite /P /Zmod_Z_Eq /modP Z.mod_mod //=.
  }
- {
  subst.
  change 255%nat with (S (Z.to_nat 254)).
  rewrite ?montgomery_rec_eq_fn_rev.
  2,3: done.
  assert(Habstr:= abstract_fn_rev_eq_c_Fp (254 + 1) 254 (Z.to_nat N) (Zmodp.pi (modP X)) N (modP X) H255 Hxxx Hnn).
  Opaque abstract_fn_rev.
  rewrite /P in Habstr.
  rewrite /Z25519_Z_Eq in Habstr.
  rewrite /val in Habstr.
  rewrite /Zmodp_subType in Habstr.
  symmetry.
  assert(Habstr2:= abstract_fn_rev_eq_c_Zmod (254 + 1) 254 N X H255).
  rewrite /P /Zmod_Z_Eq /modP Z.mod_mod in Habstr2.
  2: move => //=.
  rewrite {1 4 6 7}/modP in Habstr.
  rewrite -Habstr2 in Habstr.
  symmetry.
  rewrite -Habstr.
  remember (get_c
        (abstract_fn_rev (254 + 1) 254 (Z.to_nat N) Zmodp.one (Zmodp.pi (modP X))
           Zmodp.zero Zmodp.one Zmodp.zero Zmodp.zero (Zmodp.pi (modP X)))) as GETC.
  clear.
  have Fermat:= fermat_eq_inverse GETC.
  rewrite /modP in Fermat.
  rewrite -pow_mod //.
  }
Qed.

Lemma ZCrypto_Scalarmult_curve25519_ladder n x :
  ZCrypto_Scalarmult n x = val (curve25519_Fp_ladder (Z.to_nat (Zclamp n)) (Zmodp.pi (ZUnpack25519 x))).
Proof.
  replace (Zmodp.pi (ZUnpack25519 x)) with (Zmodp.pi (modP (ZUnpack25519 x))).
  apply ZCrypto_Scalarmult_curve25519_ladder_.
  apply val_inj => /=.
  rewrite /p -lock /=.
  rewrite /modP.
  apply Zmod_mod.
Qed.

Close Scope Z.
