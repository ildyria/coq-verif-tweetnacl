Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Low.Inv25519.

(*
sv inv25519(gf o,const gf a)
{
  gf c;
  int i;
  FOR(a,16) c[a]=a[i];
  for(i=253;i>=0;i--) {
    S(c,c);
    if(i!=2&&i!=4) M(c,c,a);
  }
  FOR(i,16) o[i]=c[i];
}
*)

Open Scope Z.

Definition inv25519_spec := 
 DECLARE _inv25519
  WITH v_o: val, v_a: val, sho : share, sha : share, o : list val, a : list Z, k : Z
  PRE [ _o OF (tptr tlg), _a OF (tptr tlg)]
        PROP  (writable_share sho; readable_share sha;
                Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) a;
                Zlength a = 16;
                Zlength o = 16)
        LOCAL (temp _o v_o; temp _a v_a)
        SEP   (nm_overlap_array_sep_2 sho sha o (mVI64 a) v_o v_a k)
  POST [ tvoid ]
        PROP (
                Zlength (Inv25519 a) = 16;
                Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) (Inv25519 a)
             )
        LOCAL()
        SEP  (nm_overlap_array_sep_2' sho sha (mVI64 (Inv25519 a)) (mVI64 a) v_o v_a k).

(* Definition init_Inv (L:list localdef) sho sha shc v_o v_a v_c o (a:list Z) k := 
  EX i : Z,
   PROP  ()
   (LOCALx L
   SEP   (nm_overlap_array_sep_2 sho sha o (mVI64 a) v_o v_a k;
          shc [{ v_c }] <<(lg16)-- (list.take (nat_of_Z i) (mVI64 a) ++ list.drop (nat_of_Z i) undef16))).
 *)
Definition inv25519_Inv sho sha shc v_o v_a v_c o (a:list Z) k :=
(* Loop Invariant *)
fun i:Z => 
  PROP (-1 <= i <= 253)
  LOCAL ((temp _i (Vint (Int.repr i)));
      temp _o v_o; temp _a v_a;
      lvar _c (tarray tlg 16) v_c)
  SEP ( nm_overlap_array_sep_2 sho sha o (mVI64 a) v_o v_a k;
        shc [{ v_c }] <<(lg16)-- (mVI64 (pow_fn_rev (253 - i) 254 a a))).

Definition inv25519_PreIncInv sho sha shc v_o v_a v_c o (a:list Z) k :=
(* PreDec invariant *)
  fun i:Z =>
  PROP (0 <= i <= 253)
  LOCAL ((temp _i (Vint (Int.repr i)));
      temp _o v_o; temp _a v_a;
      lvar _c (tarray tlg 16) v_c)
  SEP ( nm_overlap_array_sep_2 sho sha o (mVI64 a) v_o v_a k;
        shc [{ v_c }] <<(lg16)-- mVI64 (pow_fn_rev (253 - (i - 1)) 254 a a)).

Definition inv25519_PostInv sho sha shc v_o v_a v_c o (a:list Z) k :=
(* Loop postcondition *)
 PROP ()
 LOCAL (
      temp _o v_o; temp _a v_a;
      lvar _c (tarray tlg 16) v_c)
  SEP ( nm_overlap_array_sep_2 sho sha o (mVI64 a) v_o v_a k;
        shc [{ v_c }] <<(lg16)-- mVI64 (pow_fn_rev 254 254 a a)).

Definition copy_Inv (L:list localdef) sho sha shc v_o v_a v_c o (a:list Z) (c:list Z) k := 
  EX i : Z,
   PROP  ()
   (LOCALx L
   SEP   ( nm_overlap_array_sep_2' sho sha (list.take (nat_of_Z i) (mVI64 c) ++ (list.drop (nat_of_Z i) o)) (mVI64 a) v_o v_a k; 
           shc [{v_c}] <<(lg16)-- (mVI64 c))).

Close Scope Z.