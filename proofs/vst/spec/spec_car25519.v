Set Warnings "-notation-overridden,-parsing".
Require Import Tweetnacl_verif.init_tweetnacl.
Require Import Tweetnacl.Low.Car25519.
Require Import Tweetnacl.Low.Carry_n.
Require Import Tweetnacl.Low.BackCarry.

Open Scope Z.

Definition car25519_spec :=
 DECLARE _car25519
  WITH v_o: val, sh : share, o : list Z
  PRE [ _o OF (tptr tlg)]
        PROP  (writable_share sh;
                Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) o;
                Zlength o = 16)
        LOCAL (temp _o v_o)
        SEP   (sh [{ v_o }] <<(lg16)-- mVI64 o)
  POST [ tvoid ]
        PROP (
              Forall (fun x => 38 * - 2 ^ 47 <= x < 2 ^ 16 + 38 * 2 ^ 47) (car25519 o)
             )
        LOCAL()
        SEP (sh [{ v_o }] <<(lg16)-- mVI64 (car25519 o)).

Definition car25519_Inv sh v_o o := 
  EX i : Z,
   PROP  (writable_share sh;
          Forall (fun x => -Z.pow 2 62 < x < Z.pow 2 62) o;
          Zlength o = 16;
          i >= 0)
   LOCAL (temp _o v_o)
   SEP   (sh [{ v_o }] <<(lg16)-- mVI64 (if Z.ltb i 16 then (Carrying_n 16 (nat_of_Z i) 0 o) else car25519 o)).

Close Scope Z.