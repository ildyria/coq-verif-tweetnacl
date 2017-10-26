Require Import Tweetnacl.Libs.Export.
Require Import stdpp.prelude.

Require Import Tweetnacl.Mid.Inner_M1.
Require Import Tweetnacl.Mid.Outer_M1.

Local Open Scope Z.

(* Ltac inner_M_fix_compute_solve := intros ; repeat rewrite inner_M_i_j_eq by omega ; change_Z_to_nat ;
simpl ; unfold update_M_i_j' ; unfold local_update_M ;reflexivity. *)
Ltac inner_M_fix_compute_solve := intros ; repeat orewrite inner_M_i_j_eq ; simpl ; unfold update_M_i_j' ; unfold local_update_M ;reflexivity.


Lemma inner_M_fix_0_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 0 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58;
     z59; z60; z61]) =
[z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61].
Proof.  inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_1_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 1 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58;
     z59; z60]) =
[z61; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_2_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 2 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58;
     z59]) =
[z61; z60; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_3_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 3 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58]) =
[z61; z60; z59; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55; z56; z57; z58].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_4_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 4 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57]) =
[z61; z60; z59; z58; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55; z56; z57].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_5_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 5 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56]) =
[z61; z60; z59; z58; z57; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55; z56].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_6_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 6 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55]) =
[z61; z60; z59; z58; z57; z56; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54; z55].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_7_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 7 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53; z54]) =
[z61; z60; z59; z58; z57; z56; z55; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53; z54].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_8_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 8 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52; z53]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52; z53].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_9_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 9 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51; z52]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51; z52].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_10_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 10 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50; z51]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50; z51].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_11_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 11 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49; z50]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49; z50].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_12_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 12 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48; z49]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48;
z49].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_13_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 13 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z49; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47; z48]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z49; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47; z48].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_14_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 14 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z49; z48; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46; z47]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z49; z48; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46; z47].
Proof. inner_M_fix_compute_solve. Qed.

Lemma inner_M_fix_15_16 : forall z0 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  (inner_M_fix 15 16 z0
     [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28;
     z29; z30]
     [z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z49; z48; z47; z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44;
     z45; z46]) =
[z61; z60; z59; z58; z57; z56; z55; z54; z53; z52; z51; z50; z49; z48; z47; z0 * z15 + z31; z0 * z16 + z32; z0 * z17 + z33; z0 * z18 + z34;
z0 * z19 + z35; z0 * z20 + z36; z0 * z21 + z37; z0 * z22 + z38;
z0 * z23 + z39; z0 * z24 + z40; z0 * z25 + z41; z0 * z26 + z42;
z0 * z27 + z43; z0 * z28 + z44; z0 * z29 + z45; z0 * z30 + z46].
Proof. inner_M_fix_compute_solve. Qed.

Hint Rewrite inner_M_fix_0_16
inner_M_fix_1_16
inner_M_fix_2_16
inner_M_fix_3_16
inner_M_fix_4_16
inner_M_fix_5_16
inner_M_fix_6_16
inner_M_fix_7_16
inner_M_fix_8_16
inner_M_fix_9_16
inner_M_fix_10_16
inner_M_fix_11_16
inner_M_fix_12_16
inner_M_fix_13_16
inner_M_fix_14_16
inner_M_fix_15_16 : innerouterMdb.

Lemma outer_M_fix_0_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 0 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
  [z * z15 + z31; z * z16 + z32; z * z17 + z33; z * z18 + z34; z * z19 + z35;
  z * z20 + z36; z * z21 + z37; z * z22 + z38; z * z23 + z39; z * z24 + z40;
  z * z25 + z41; z * z26 + z42; z * z27 + z43; z * z28 + z44; z * z29 + z45;
  z * z30 + z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58;
  z59; z60; z61].
Proof. intros; repeat orewrite outer_M_i_j_eq; reflexivity. Qed.

Hint Rewrite outer_M_fix_0_16 : innerouterMdb.

Ltac outer_M_fix_compute_solve := intros ;
rewrite outer_M_fix_equation ; flatten ; tryfalse ; autorewrite with innerouterMdb ;
reflexivity.


Lemma outer_M_fix_1_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 1 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32); z * z17 + (z0 * z16 + z33);
z * z18 + (z0 * z17 + z34); z * z19 + (z0 * z18 + z35);
z * z20 + (z0 * z19 + z36); z * z21 + (z0 * z20 + z37);
z * z22 + (z0 * z21 + z38); z * z23 + (z0 * z22 + z39);
z * z24 + (z0 * z23 + z40); z * z25 + (z0 * z24 + z41);
z * z26 + (z0 * z25 + z42); z * z27 + (z0 * z26 + z43);
z * z28 + (z0 * z27 + z44); z * z29 + (z0 * z28 + z45);
z * z30 + (z0 * z29 + z46); z0 * z30 + z47; z48; z49; z50; z51; z52; z53;
z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_1_16 : innerouterMdb.

Lemma outer_M_fix_2_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 2 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + z34));
z * z19 + (z0 * z18 + (z1 * z17 + z35));
z * z20 + (z0 * z19 + (z1 * z18 + z36));
z * z21 + (z0 * z20 + (z1 * z19 + z37));
z * z22 + (z0 * z21 + (z1 * z20 + z38));
z * z23 + (z0 * z22 + (z1 * z21 + z39));
z * z24 + (z0 * z23 + (z1 * z22 + z40));
z * z25 + (z0 * z24 + (z1 * z23 + z41));
z * z26 + (z0 * z25 + (z1 * z24 + z42));
z * z27 + (z0 * z26 + (z1 * z25 + z43));
z * z28 + (z0 * z27 + (z1 * z26 + z44));
z * z29 + (z0 * z28 + (z1 * z27 + z45));
z * z30 + (z0 * z29 + (z1 * z28 + z46)); z0 * z30 + (z1 * z29 + z47);
z1 * z30 + z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60;
z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_2_16 : innerouterMdb.

Lemma outer_M_fix_3_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 3 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + z35)));
z * z20 + (z0 * z19 + (z1 * z18 + (z2 * z17 + z36)));
z * z21 + (z0 * z20 + (z1 * z19 + (z2 * z18 + z37)));
z * z22 + (z0 * z21 + (z1 * z20 + (z2 * z19 + z38)));
z * z23 + (z0 * z22 + (z1 * z21 + (z2 * z20 + z39)));
z * z24 + (z0 * z23 + (z1 * z22 + (z2 * z21 + z40)));
z * z25 + (z0 * z24 + (z1 * z23 + (z2 * z22 + z41)));
z * z26 + (z0 * z25 + (z1 * z24 + (z2 * z23 + z42)));
z * z27 + (z0 * z26 + (z1 * z25 + (z2 * z24 + z43)));
z * z28 + (z0 * z27 + (z1 * z26 + (z2 * z25 + z44)));
z * z29 + (z0 * z28 + (z1 * z27 + (z2 * z26 + z45)));
z * z30 + (z0 * z29 + (z1 * z28 + (z2 * z27 + z46)));
z0 * z30 + (z1 * z29 + (z2 * z28 + z47)); z1 * z30 + (z2 * z29 + z48);
z2 * z30 + z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_3_16 : innerouterMdb.

Lemma outer_M_fix_4_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 4 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 + (z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + z36))));
z * z21 + (z0 * z20 + (z1 * z19 + (z2 * z18 + (z3 * z17 + z37))));
z * z22 + (z0 * z21 + (z1 * z20 + (z2 * z19 + (z3 * z18 + z38))));
z * z23 + (z0 * z22 + (z1 * z21 + (z2 * z20 + (z3 * z19 + z39))));
z * z24 + (z0 * z23 + (z1 * z22 + (z2 * z21 + (z3 * z20 + z40))));
z * z25 + (z0 * z24 + (z1 * z23 + (z2 * z22 + (z3 * z21 + z41))));
z * z26 + (z0 * z25 + (z1 * z24 + (z2 * z23 + (z3 * z22 + z42))));
z * z27 + (z0 * z26 + (z1 * z25 + (z2 * z24 + (z3 * z23 + z43))));
z * z28 + (z0 * z27 + (z1 * z26 + (z2 * z25 + (z3 * z24 + z44))));
z * z29 + (z0 * z28 + (z1 * z27 + (z2 * z26 + (z3 * z25 + z45))));
z * z30 + (z0 * z29 + (z1 * z28 + (z2 * z27 + (z3 * z26 + z46))));
z0 * z30 + (z1 * z29 + (z2 * z28 + (z3 * z27 + z47)));
z1 * z30 + (z2 * z29 + (z3 * z28 + z48)); z2 * z30 + (z3 * z29 + z49);
z3 * z30 + z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_4_16 : innerouterMdb.

Lemma outer_M_fix_5_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 5 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 + (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + z37)))));
z * z22 +
(z0 * z21 + (z1 * z20 + (z2 * z19 + (z3 * z18 + (z4 * z17 + z38)))));
z * z23 +
(z0 * z22 + (z1 * z21 + (z2 * z20 + (z3 * z19 + (z4 * z18 + z39)))));
z * z24 +
(z0 * z23 + (z1 * z22 + (z2 * z21 + (z3 * z20 + (z4 * z19 + z40)))));
z * z25 +
(z0 * z24 + (z1 * z23 + (z2 * z22 + (z3 * z21 + (z4 * z20 + z41)))));
z * z26 +
(z0 * z25 + (z1 * z24 + (z2 * z23 + (z3 * z22 + (z4 * z21 + z42)))));
z * z27 +
(z0 * z26 + (z1 * z25 + (z2 * z24 + (z3 * z23 + (z4 * z22 + z43)))));
z * z28 +
(z0 * z27 + (z1 * z26 + (z2 * z25 + (z3 * z24 + (z4 * z23 + z44)))));
z * z29 +
(z0 * z28 + (z1 * z27 + (z2 * z26 + (z3 * z25 + (z4 * z24 + z45)))));
z * z30 +
(z0 * z29 + (z1 * z28 + (z2 * z27 + (z3 * z26 + (z4 * z25 + z46)))));
z0 * z30 + (z1 * z29 + (z2 * z28 + (z3 * z27 + (z4 * z26 + z47))));
z1 * z30 + (z2 * z29 + (z3 * z28 + (z4 * z27 + z48)));
z2 * z30 + (z3 * z29 + (z4 * z28 + z49)); z3 * z30 + (z4 * z29 + z50);
z4 * z30 + z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_5_16 : innerouterMdb.

Lemma outer_M_fix_6_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 6 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30]
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 + (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + z38))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 + (z2 * z20 + (z3 * z19 + (z4 * z18 + (z5 * z17 + z39))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 + (z2 * z21 + (z3 * z20 + (z4 * z19 + (z5 * z18 + z40))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 + (z2 * z22 + (z3 * z21 + (z4 * z20 + (z5 * z19 + z41))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 + (z2 * z23 + (z3 * z22 + (z4 * z21 + (z5 * z20 + z42))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 + (z2 * z24 + (z3 * z23 + (z4 * z22 + (z5 * z21 + z43))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 + (z2 * z25 + (z3 * z24 + (z4 * z23 + (z5 * z22 + z44))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 + (z2 * z26 + (z3 * z25 + (z4 * z24 + (z5 * z23 + z45))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 + (z2 * z27 + (z3 * z26 + (z4 * z25 + (z5 * z24 + z46))))));
z0 * z30 +
(z1 * z29 + (z2 * z28 + (z3 * z27 + (z4 * z26 + (z5 * z25 + z47)))));
z1 * z30 + (z2 * z29 + (z3 * z28 + (z4 * z27 + (z5 * z26 + z48))));
z2 * z30 + (z3 * z29 + (z4 * z28 + (z5 * z27 + z49)));
z3 * z30 + (z4 * z29 + (z5 * z28 + z50)); z4 * z30 + (z5 * z29 + z51);
z5 * z30 + z52; z53; z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_6_16 : innerouterMdb.

Lemma outer_M_fix_7_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 7 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 + (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + z39)))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 + (z3 * z20 + (z4 * z19 + (z5 * z18 + (z6 * z17 + z40)))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 + (z3 * z21 + (z4 * z20 + (z5 * z19 + (z6 * z18 + z41)))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 + (z3 * z22 + (z4 * z21 + (z5 * z20 + (z6 * z19 + z42)))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 + (z3 * z23 + (z4 * z22 + (z5 * z21 + (z6 * z20 + z43)))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 + (z3 * z24 + (z4 * z23 + (z5 * z22 + (z6 * z21 + z44)))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 + (z3 * z25 + (z4 * z24 + (z5 * z23 + (z6 * z22 + z45)))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 + (z3 * z26 + (z4 * z25 + (z5 * z24 + (z6 * z23 + z46)))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 + (z3 * z27 + (z4 * z26 + (z5 * z25 + (z6 * z24 + z47))))));
z1 * z30 +
(z2 * z29 + (z3 * z28 + (z4 * z27 + (z5 * z26 + (z6 * z25 + z48)))));
z2 * z30 + (z3 * z29 + (z4 * z28 + (z5 * z27 + (z6 * z26 + z49))));
z3 * z30 + (z4 * z29 + (z5 * z28 + (z6 * z27 + z50)));
z4 * z30 + (z5 * z29 + (z6 * z28 + z51)); z5 * z30 + (z6 * z29 + z52);
z6 * z30 + z53; z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_7_16 : innerouterMdb.

Lemma outer_M_fix_8_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 8 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 + (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + z40))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 + (z4 * z20 + (z5 * z19 + (z6 * z18 + (z7 * z17 + z41))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 + (z4 * z21 + (z5 * z20 + (z6 * z19 + (z7 * z18 + z42))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 + (z4 * z22 + (z5 * z21 + (z6 * z20 + (z7 * z19 + z43))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 + (z4 * z23 + (z5 * z22 + (z6 * z21 + (z7 * z20 + z44))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 + (z4 * z24 + (z5 * z23 + (z6 * z22 + (z7 * z21 + z45))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 + (z4 * z25 + (z5 * z24 + (z6 * z23 + (z7 * z22 + z46))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 + (z4 * z26 + (z5 * z25 + (z6 * z24 + (z7 * z23 + z47)))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 + (z4 * z27 + (z5 * z26 + (z6 * z25 + (z7 * z24 + z48))))));
z2 * z30 +
(z3 * z29 + (z4 * z28 + (z5 * z27 + (z6 * z26 + (z7 * z25 + z49)))));
z3 * z30 + (z4 * z29 + (z5 * z28 + (z6 * z27 + (z7 * z26 + z50))));
z4 * z30 + (z5 * z29 + (z6 * z28 + (z7 * z27 + z51)));
z5 * z30 + (z6 * z29 + (z7 * z28 + z52)); z6 * z30 + (z7 * z29 + z53);
z7 * z30 + z54; z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_8_16 : innerouterMdb.

Lemma outer_M_fix_9_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 9 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 + (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + z41)))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 + (z5 * z20 + (z6 * z19 + (z7 * z18 + (z8 * z17 + z42)))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 + (z5 * z21 + (z6 * z20 + (z7 * z19 + (z8 * z18 + z43)))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 + (z5 * z22 + (z6 * z21 + (z7 * z20 + (z8 * z19 + z44)))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 + (z5 * z23 + (z6 * z22 + (z7 * z21 + (z8 * z20 + z45)))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 + (z5 * z24 + (z6 * z23 + (z7 * z22 + (z8 * z21 + z46)))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 + (z5 * z25 + (z6 * z24 + (z7 * z23 + (z8 * z22 + z47))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 + (z5 * z26 + (z6 * z25 + (z7 * z24 + (z8 * z23 + z48)))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 + (z5 * z27 + (z6 * z26 + (z7 * z25 + (z8 * z24 + z49))))));
z3 * z30 +
(z4 * z29 + (z5 * z28 + (z6 * z27 + (z7 * z26 + (z8 * z25 + z50)))));
z4 * z30 + (z5 * z29 + (z6 * z28 + (z7 * z27 + (z8 * z26 + z51))));
z5 * z30 + (z6 * z29 + (z7 * z28 + (z8 * z27 + z52)));
z6 * z30 + (z7 * z29 + (z8 * z28 + z53)); z7 * z30 + (z8 * z29 + z54);
z8 * z30 + z55; z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_9_16 : innerouterMdb.

Lemma outer_M_fix_10_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 10 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 +
     (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + (z9 * z15 + z41))))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 +
     (z5 * z20 + (z6 * z19 + (z7 * z18 + (z8 * z17 + (z9 * z16 + z42))))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 +
     (z5 * z21 + (z6 * z20 + (z7 * z19 + (z8 * z18 + (z9 * z17 + z43))))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 +
     (z5 * z22 + (z6 * z21 + (z7 * z20 + (z8 * z19 + (z9 * z18 + z44))))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 +
     (z5 * z23 + (z6 * z22 + (z7 * z21 + (z8 * z20 + (z9 * z19 + z45))))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 +
     (z5 * z24 + (z6 * z23 + (z7 * z22 + (z8 * z21 + (z9 * z20 + z46))))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 +
    (z5 * z25 + (z6 * z24 + (z7 * z23 + (z8 * z22 + (z9 * z21 + z47)))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 +
   (z5 * z26 + (z6 * z25 + (z7 * z24 + (z8 * z23 + (z9 * z22 + z48))))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 +
  (z5 * z27 + (z6 * z26 + (z7 * z25 + (z8 * z24 + (z9 * z23 + z49)))))));
z3 * z30 +
(z4 * z29 +
 (z5 * z28 + (z6 * z27 + (z7 * z26 + (z8 * z25 + (z9 * z24 + z50))))));
z4 * z30 +
(z5 * z29 + (z6 * z28 + (z7 * z27 + (z8 * z26 + (z9 * z25 + z51)))));
z5 * z30 + (z6 * z29 + (z7 * z28 + (z8 * z27 + (z9 * z26 + z52))));
z6 * z30 + (z7 * z29 + (z8 * z28 + (z9 * z27 + z53)));
z7 * z30 + (z8 * z29 + (z9 * z28 + z54)); z8 * z30 + (z9 * z29 + z55);
z9 * z30 + z56; z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_10_16 : innerouterMdb.

Lemma outer_M_fix_11_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 11 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] = 
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 +
     (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + (z9 * z15 + z41))))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 +
     (z5 * z20 +
      (z6 * z19 + (z7 * z18 + (z8 * z17 + (z9 * z16 + (z10 * z15 + z42)))))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 +
     (z5 * z21 +
      (z6 * z20 + (z7 * z19 + (z8 * z18 + (z9 * z17 + (z10 * z16 + z43)))))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 +
     (z5 * z22 +
      (z6 * z21 + (z7 * z20 + (z8 * z19 + (z9 * z18 + (z10 * z17 + z44)))))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 +
     (z5 * z23 +
      (z6 * z22 + (z7 * z21 + (z8 * z20 + (z9 * z19 + (z10 * z18 + z45)))))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 +
     (z5 * z24 +
      (z6 * z23 + (z7 * z22 + (z8 * z21 + (z9 * z20 + (z10 * z19 + z46)))))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 +
    (z5 * z25 +
     (z6 * z24 + (z7 * z23 + (z8 * z22 + (z9 * z21 + (z10 * z20 + z47))))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 +
   (z5 * z26 +
    (z6 * z25 + (z7 * z24 + (z8 * z23 + (z9 * z22 + (z10 * z21 + z48)))))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 +
  (z5 * z27 +
   (z6 * z26 + (z7 * z25 + (z8 * z24 + (z9 * z23 + (z10 * z22 + z49))))))));
z3 * z30 +
(z4 * z29 +
 (z5 * z28 +
  (z6 * z27 + (z7 * z26 + (z8 * z25 + (z9 * z24 + (z10 * z23 + z50)))))));
z4 * z30 +
(z5 * z29 +
 (z6 * z28 + (z7 * z27 + (z8 * z26 + (z9 * z25 + (z10 * z24 + z51))))));
z5 * z30 +
(z6 * z29 + (z7 * z28 + (z8 * z27 + (z9 * z26 + (z10 * z25 + z52)))));
z6 * z30 + (z7 * z29 + (z8 * z28 + (z9 * z27 + (z10 * z26 + z53))));
z7 * z30 + (z8 * z29 + (z9 * z28 + (z10 * z27 + z54)));
z8 * z30 + (z9 * z29 + (z10 * z28 + z55)); z9 * z30 + (z10 * z29 + z56);
z10 * z30 + z57; z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_11_16 : innerouterMdb.

Lemma outer_M_fix_12_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 12 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] =
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 +
     (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + (z9 * z15 + z41))))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 +
     (z5 * z20 +
      (z6 * z19 + (z7 * z18 + (z8 * z17 + (z9 * z16 + (z10 * z15 + z42)))))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 +
     (z5 * z21 +
      (z6 * z20 +
       (z7 * z19 + (z8 * z18 + (z9 * z17 + (z10 * z16 + (z11 * z15 + z43))))))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 +
     (z5 * z22 +
      (z6 * z21 +
       (z7 * z20 + (z8 * z19 + (z9 * z18 + (z10 * z17 + (z11 * z16 + z44))))))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 +
     (z5 * z23 +
      (z6 * z22 +
       (z7 * z21 + (z8 * z20 + (z9 * z19 + (z10 * z18 + (z11 * z17 + z45))))))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 +
     (z5 * z24 +
      (z6 * z23 +
       (z7 * z22 + (z8 * z21 + (z9 * z20 + (z10 * z19 + (z11 * z18 + z46))))))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 +
    (z5 * z25 +
     (z6 * z24 +
      (z7 * z23 + (z8 * z22 + (z9 * z21 + (z10 * z20 + (z11 * z19 + z47)))))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 +
   (z5 * z26 +
    (z6 * z25 +
     (z7 * z24 + (z8 * z23 + (z9 * z22 + (z10 * z21 + (z11 * z20 + z48))))))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 +
  (z5 * z27 +
   (z6 * z26 +
    (z7 * z25 + (z8 * z24 + (z9 * z23 + (z10 * z22 + (z11 * z21 + z49)))))))));
z3 * z30 +
(z4 * z29 +
 (z5 * z28 +
  (z6 * z27 +
   (z7 * z26 + (z8 * z25 + (z9 * z24 + (z10 * z23 + (z11 * z22 + z50))))))));
z4 * z30 +
(z5 * z29 +
 (z6 * z28 +
  (z7 * z27 + (z8 * z26 + (z9 * z25 + (z10 * z24 + (z11 * z23 + z51)))))));
z5 * z30 +
(z6 * z29 +
 (z7 * z28 + (z8 * z27 + (z9 * z26 + (z10 * z25 + (z11 * z24 + z52))))));
z6 * z30 +
(z7 * z29 + (z8 * z28 + (z9 * z27 + (z10 * z26 + (z11 * z25 + z53)))));
z7 * z30 + (z8 * z29 + (z9 * z28 + (z10 * z27 + (z11 * z26 + z54))));
z8 * z30 + (z9 * z29 + (z10 * z28 + (z11 * z27 + z55)));
z9 * z30 + (z10 * z29 + (z11 * z28 + z56)); z10 * z30 + (z11 * z29 + z57);
z11 * z30 + z58; z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_12_16 : innerouterMdb.

Lemma outer_M_fix_13_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 13 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] =
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 +
     (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + (z9 * z15 + z41))))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 +
     (z5 * z20 +
      (z6 * z19 + (z7 * z18 + (z8 * z17 + (z9 * z16 + (z10 * z15 + z42)))))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 +
     (z5 * z21 +
      (z6 * z20 +
       (z7 * z19 + (z8 * z18 + (z9 * z17 + (z10 * z16 + (z11 * z15 + z43))))))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 +
     (z5 * z22 +
      (z6 * z21 +
       (z7 * z20 +
        (z8 * z19 +
         (z9 * z18 + (z10 * z17 + (z11 * z16 + (z12 * z15 + z44)))))))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 +
     (z5 * z23 +
      (z6 * z22 +
       (z7 * z21 +
        (z8 * z20 +
         (z9 * z19 + (z10 * z18 + (z11 * z17 + (z12 * z16 + z45)))))))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 +
     (z5 * z24 +
      (z6 * z23 +
       (z7 * z22 +
        (z8 * z21 +
         (z9 * z20 + (z10 * z19 + (z11 * z18 + (z12 * z17 + z46)))))))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 +
    (z5 * z25 +
     (z6 * z24 +
      (z7 * z23 +
       (z8 * z22 + (z9 * z21 + (z10 * z20 + (z11 * z19 + (z12 * z18 + z47))))))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 +
   (z5 * z26 +
    (z6 * z25 +
     (z7 * z24 +
      (z8 * z23 + (z9 * z22 + (z10 * z21 + (z11 * z20 + (z12 * z19 + z48)))))))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 +
  (z5 * z27 +
   (z6 * z26 +
    (z7 * z25 +
     (z8 * z24 + (z9 * z23 + (z10 * z22 + (z11 * z21 + (z12 * z20 + z49))))))))));
z3 * z30 +
(z4 * z29 +
 (z5 * z28 +
  (z6 * z27 +
   (z7 * z26 +
    (z8 * z25 + (z9 * z24 + (z10 * z23 + (z11 * z22 + (z12 * z21 + z50)))))))));
z4 * z30 +
(z5 * z29 +
 (z6 * z28 +
  (z7 * z27 +
   (z8 * z26 + (z9 * z25 + (z10 * z24 + (z11 * z23 + (z12 * z22 + z51))))))));
z5 * z30 +
(z6 * z29 +
 (z7 * z28 +
  (z8 * z27 + (z9 * z26 + (z10 * z25 + (z11 * z24 + (z12 * z23 + z52)))))));
z6 * z30 +
(z7 * z29 +
 (z8 * z28 + (z9 * z27 + (z10 * z26 + (z11 * z25 + (z12 * z24 + z53))))));
z7 * z30 +
(z8 * z29 + (z9 * z28 + (z10 * z27 + (z11 * z26 + (z12 * z25 + z54)))));
z8 * z30 + (z9 * z29 + (z10 * z28 + (z11 * z27 + (z12 * z26 + z55))));
z9 * z30 + (z10 * z29 + (z11 * z28 + (z12 * z27 + z56)));
z10 * z30 + (z11 * z29 + (z12 * z28 + z57)); z11 * z30 + (z12 * z29 + z58);
z12 * z30 + z59; z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_13_16 : innerouterMdb.

Lemma outer_M_fix_14_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 14 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] =
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 +
     (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + (z9 * z15 + z41))))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 +
     (z5 * z20 +
      (z6 * z19 + (z7 * z18 + (z8 * z17 + (z9 * z16 + (z10 * z15 + z42)))))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 +
     (z5 * z21 +
      (z6 * z20 +
       (z7 * z19 + (z8 * z18 + (z9 * z17 + (z10 * z16 + (z11 * z15 + z43))))))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 +
     (z5 * z22 +
      (z6 * z21 +
       (z7 * z20 +
        (z8 * z19 +
         (z9 * z18 + (z10 * z17 + (z11 * z16 + (z12 * z15 + z44)))))))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 +
     (z5 * z23 +
      (z6 * z22 +
       (z7 * z21 +
        (z8 * z20 +
         (z9 * z19 +
          (z10 * z18 + (z11 * z17 + (z12 * z16 + (z13 * z15 + z45))))))))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 +
     (z5 * z24 +
      (z6 * z23 +
       (z7 * z22 +
        (z8 * z21 +
         (z9 * z20 +
          (z10 * z19 + (z11 * z18 + (z12 * z17 + (z13 * z16 + z46))))))))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 +
    (z5 * z25 +
     (z6 * z24 +
      (z7 * z23 +
       (z8 * z22 +
        (z9 * z21 +
         (z10 * z20 + (z11 * z19 + (z12 * z18 + (z13 * z17 + z47)))))))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 +
   (z5 * z26 +
    (z6 * z25 +
     (z7 * z24 +
      (z8 * z23 +
       (z9 * z22 +
        (z10 * z21 + (z11 * z20 + (z12 * z19 + (z13 * z18 + z48))))))))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 +
  (z5 * z27 +
   (z6 * z26 +
    (z7 * z25 +
     (z8 * z24 +
      (z9 * z23 + (z10 * z22 + (z11 * z21 + (z12 * z20 + (z13 * z19 + z49)))))))))));
z3 * z30 +
(z4 * z29 +
 (z5 * z28 +
  (z6 * z27 +
   (z7 * z26 +
    (z8 * z25 +
     (z9 * z24 + (z10 * z23 + (z11 * z22 + (z12 * z21 + (z13 * z20 + z50))))))))));
z4 * z30 +
(z5 * z29 +
 (z6 * z28 +
  (z7 * z27 +
   (z8 * z26 +
    (z9 * z25 + (z10 * z24 + (z11 * z23 + (z12 * z22 + (z13 * z21 + z51)))))))));
z5 * z30 +
(z6 * z29 +
 (z7 * z28 +
  (z8 * z27 +
   (z9 * z26 + (z10 * z25 + (z11 * z24 + (z12 * z23 + (z13 * z22 + z52))))))));
z6 * z30 +
(z7 * z29 +
 (z8 * z28 +
  (z9 * z27 + (z10 * z26 + (z11 * z25 + (z12 * z24 + (z13 * z23 + z53)))))));
z7 * z30 +
(z8 * z29 +
 (z9 * z28 + (z10 * z27 + (z11 * z26 + (z12 * z25 + (z13 * z24 + z54))))));
z8 * z30 +
(z9 * z29 + (z10 * z28 + (z11 * z27 + (z12 * z26 + (z13 * z25 + z55)))));
z9 * z30 + (z10 * z29 + (z11 * z28 + (z12 * z27 + (z13 * z26 + z56))));
z10 * z30 + (z11 * z29 + (z12 * z28 + (z13 * z27 + z57)));
z11 * z30 + (z12 * z29 + (z13 * z28 + z58)); z12 * z30 + (z13 * z29 + z59);
z13 * z30 + z60; z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_14_16 : innerouterMdb.

Lemma outer_M_fix_15_16: forall z z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29
  z30 z31 z32 z33 z34 z35 z36 z37 z38 z39 z40 z41 z42 z43 z44 z45 z46 z47 z48 z49 z50 z51 z52 z53 z54 z55 z56 z57 z58 z59 z60 z61,
  outer_M_fix 15 16
  [z; z0; z1; z2; z3; z4; z5; z6; z7; z8; z9; z10; z11; z12; z13; z14]
  [z15; z16; z17; z18; z19; z20; z21; z22; z23; z24; z25; z26; z27; z28; z29;
  z30] 
  [z31; z32; z33; z34; z35; z36; z37; z38; z39; z40; z41; z42; z43; z44; z45; z46; z47; z48; z49; z50; z51; z52; z53; z54; z55; z56; z57; z58; z59; z60; z61] =
[z * z15 + z31; z * z16 + (z0 * z15 + z32);
z * z17 + (z0 * z16 + (z1 * z15 + z33));
z * z18 + (z0 * z17 + (z1 * z16 + (z2 * z15 + z34)));
z * z19 + (z0 * z18 + (z1 * z17 + (z2 * z16 + (z3 * z15 + z35))));
z * z20 +
(z0 * z19 + (z1 * z18 + (z2 * z17 + (z3 * z16 + (z4 * z15 + z36)))));
z * z21 +
(z0 * z20 +
 (z1 * z19 + (z2 * z18 + (z3 * z17 + (z4 * z16 + (z5 * z15 + z37))))));
z * z22 +
(z0 * z21 +
 (z1 * z20 +
  (z2 * z19 + (z3 * z18 + (z4 * z17 + (z5 * z16 + (z6 * z15 + z38)))))));
z * z23 +
(z0 * z22 +
 (z1 * z21 +
  (z2 * z20 +
   (z3 * z19 + (z4 * z18 + (z5 * z17 + (z6 * z16 + (z7 * z15 + z39))))))));
z * z24 +
(z0 * z23 +
 (z1 * z22 +
  (z2 * z21 +
   (z3 * z20 +
    (z4 * z19 + (z5 * z18 + (z6 * z17 + (z7 * z16 + (z8 * z15 + z40)))))))));
z * z25 +
(z0 * z24 +
 (z1 * z23 +
  (z2 * z22 +
   (z3 * z21 +
    (z4 * z20 +
     (z5 * z19 + (z6 * z18 + (z7 * z17 + (z8 * z16 + (z9 * z15 + z41))))))))));
z * z26 +
(z0 * z25 +
 (z1 * z24 +
  (z2 * z23 +
   (z3 * z22 +
    (z4 * z21 +
     (z5 * z20 +
      (z6 * z19 + (z7 * z18 + (z8 * z17 + (z9 * z16 + (z10 * z15 + z42)))))))))));
z * z27 +
(z0 * z26 +
 (z1 * z25 +
  (z2 * z24 +
   (z3 * z23 +
    (z4 * z22 +
     (z5 * z21 +
      (z6 * z20 +
       (z7 * z19 + (z8 * z18 + (z9 * z17 + (z10 * z16 + (z11 * z15 + z43))))))))))));
z * z28 +
(z0 * z27 +
 (z1 * z26 +
  (z2 * z25 +
   (z3 * z24 +
    (z4 * z23 +
     (z5 * z22 +
      (z6 * z21 +
       (z7 * z20 +
        (z8 * z19 +
         (z9 * z18 + (z10 * z17 + (z11 * z16 + (z12 * z15 + z44)))))))))))));
z * z29 +
(z0 * z28 +
 (z1 * z27 +
  (z2 * z26 +
   (z3 * z25 +
    (z4 * z24 +
     (z5 * z23 +
      (z6 * z22 +
       (z7 * z21 +
        (z8 * z20 +
         (z9 * z19 +
          (z10 * z18 + (z11 * z17 + (z12 * z16 + (z13 * z15 + z45))))))))))))));
z * z30 +
(z0 * z29 +
 (z1 * z28 +
  (z2 * z27 +
   (z3 * z26 +
    (z4 * z25 +
     (z5 * z24 +
      (z6 * z23 +
       (z7 * z22 +
        (z8 * z21 +
         (z9 * z20 +
          (z10 * z19 +
           (z11 * z18 + (z12 * z17 + (z13 * z16 + (z14 * z15 + z46)))))))))))))));
z0 * z30 +
(z1 * z29 +
 (z2 * z28 +
  (z3 * z27 +
   (z4 * z26 +
    (z5 * z25 +
     (z6 * z24 +
      (z7 * z23 +
       (z8 * z22 +
        (z9 * z21 +
         (z10 * z20 +
          (z11 * z19 + (z12 * z18 + (z13 * z17 + (z14 * z16 + z47))))))))))))));
z1 * z30 +
(z2 * z29 +
 (z3 * z28 +
  (z4 * z27 +
   (z5 * z26 +
    (z6 * z25 +
     (z7 * z24 +
      (z8 * z23 +
       (z9 * z22 +
        (z10 * z21 +
         (z11 * z20 + (z12 * z19 + (z13 * z18 + (z14 * z17 + z48)))))))))))));
z2 * z30 +
(z3 * z29 +
 (z4 * z28 +
  (z5 * z27 +
   (z6 * z26 +
    (z7 * z25 +
     (z8 * z24 +
      (z9 * z23 +
       (z10 * z22 +
        (z11 * z21 + (z12 * z20 + (z13 * z19 + (z14 * z18 + z49))))))))))));
z3 * z30 +
(z4 * z29 +
 (z5 * z28 +
  (z6 * z27 +
   (z7 * z26 +
    (z8 * z25 +
     (z9 * z24 +
      (z10 * z23 +
       (z11 * z22 + (z12 * z21 + (z13 * z20 + (z14 * z19 + z50)))))))))));
z4 * z30 +
(z5 * z29 +
 (z6 * z28 +
  (z7 * z27 +
   (z8 * z26 +
    (z9 * z25 +
     (z10 * z24 + (z11 * z23 + (z12 * z22 + (z13 * z21 + (z14 * z20 + z51))))))))));
z5 * z30 +
(z6 * z29 +
 (z7 * z28 +
  (z8 * z27 +
   (z9 * z26 +
    (z10 * z25 + (z11 * z24 + (z12 * z23 + (z13 * z22 + (z14 * z21 + z52)))))))));
z6 * z30 +
(z7 * z29 +
 (z8 * z28 +
  (z9 * z27 +
   (z10 * z26 + (z11 * z25 + (z12 * z24 + (z13 * z23 + (z14 * z22 + z53))))))));
z7 * z30 +
(z8 * z29 +
 (z9 * z28 +
  (z10 * z27 + (z11 * z26 + (z12 * z25 + (z13 * z24 + (z14 * z23 + z54)))))));
z8 * z30 +
(z9 * z29 +
 (z10 * z28 + (z11 * z27 + (z12 * z26 + (z13 * z25 + (z14 * z24 + z55))))));
z9 * z30 +
(z10 * z29 + (z11 * z28 + (z12 * z27 + (z13 * z26 + (z14 * z25 + z56)))));
z10 * z30 + (z11 * z29 + (z12 * z28 + (z13 * z27 + (z14 * z26 + z57))));
z11 * z30 + (z12 * z29 + (z13 * z28 + (z14 * z27 + z58)));
z12 * z30 + (z13 * z29 + (z14 * z28 + z59)); z13 * z30 + (z14 * z29 + z60);
z14 * z30 + z61].
Proof. outer_M_fix_compute_solve. Qed.

Hint Rewrite outer_M_fix_15_16 : innerouterMdb.
