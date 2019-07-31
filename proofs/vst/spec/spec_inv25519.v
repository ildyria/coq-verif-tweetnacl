Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Low.Inv25519.

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
}*)

Open Scope Z.

Definition inv25519_spec := 
 DECLARE _inv25519
  WITH v_o: val, v_i: val, sho : share, shi : share, o : list val, i : list Z, k : Z
  PRE [ _o OF (tptr tlg), _i OF (tptr tlg)]
        PROP  (writable_share sho; readable_share shi;
                Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) i;
                Zlength i = 16;
                Zlength o = 16)
        LOCAL (temp _o v_o; temp _i v_i)
        SEP   (nm_overlap_array_sep_2 sho shi o (mVI64 i) v_o v_i k)
  POST [ tvoid ]
        PROP (
                Zlength (Inv25519 i) = 16;
                Forall (fun x : ℤ => -38 <= x < 2 ^ 16 + 38) (Inv25519 i)
             )
        LOCAL()
        SEP  (nm_overlap_array_sep_2' sho shi (mVI64 (Inv25519 i)) (mVI64 i) v_o v_i k).


Definition inv25519_Inv sho shi shc v_o v_i v_c o (i:list Z) k :=
(* Loop Invariant *)
fun a:Z => 
  PROP (-1 <= a <= 253)
  LOCAL ((temp _a (Vint (Int.repr a)));
      temp _o v_o; temp _i v_i;
      lvar _c (tarray tlg 16) v_c)
  SEP ( nm_overlap_array_sep_2 sho shi o (mVI64 i) v_o v_i k;
        shc [{ v_c }] <<(lg16)-- (mVI64 (pow_fn_rev (253 - a) 254 i i))).

Definition inv25519_PreIncInv sho shi shc v_o v_i v_c o (i:list Z) k :=
(* PreDec invariant *)
  fun a:Z =>
  PROP (0 <= a <= 253)
  LOCAL ((temp _a (Vint (Int.repr a)));
      temp _o v_o; temp _i v_i;
      lvar _c (tarray tlg 16) v_c)
  SEP ( nm_overlap_array_sep_2 sho shi o (mVI64 i) v_o v_i k;
        shc [{ v_c }] <<(lg16)-- mVI64 (pow_fn_rev (253 - (a - 1)) 254 i i)).

Definition inv25519_PostInv sho shi shc v_o v_i v_c o (i:list Z) k :=
(* Loop postcondition *)
 PROP ()
 LOCAL (
      temp _o v_o; temp _i v_i;
      lvar _c (tarray tlg 16) v_c)
  SEP ( nm_overlap_array_sep_2 sho shi o (mVI64 i) v_o v_i k;
        shc [{ v_c }] <<(lg16)-- mVI64 (pow_fn_rev 254 254 i i)).

Definition copy_Inv (L:list localdef) sho shi shc v_o v_i v_c o (i:list Z) (c:list Z) k := 
  EX a : Z,
   PROP  ()
   (LOCALx L
   SEP   ( nm_overlap_array_sep_2' sho shi (list.take (nat_of_Z a) (mVI64 c) ++ (list.drop (nat_of_Z a) o)) (mVI64 i) v_o v_i k; 
           shc [{v_c}] <<(lg16)-- (mVI64 c))).

Close Scope Z.