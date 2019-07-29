Set Warnings "-notation-overridden,-parsing".
From VST Require Import floyd.proofauto. (* Import the Verifiable C system *)
(* The next line is "boilerplate", always required after importing an AST. *)
Require Export Coq.ZArith.BinInt.
Require Export Coq.ZArith.Zdiv.
Require Export ssreflect.

From Tweetnacl Require Import Libs.Export.
From Tweetnacl.Low Require Import Constant.

Open Scope Z.

Theorem upd_Znth_upd_nth: forall A i (l: list A) (v:A), 0 <= i -> upd_Znth i l v = upd_nth (Z.to_nat i) l v.
Proof.
  intros A i l v Hi; gen l v.
  apply (natlike_ind (fun i => forall (l : list A) (v : A), upd_Znth i l v = upd_nth (Z.to_nat i) l v)) ; try omega.
  intros ; destruct l ; go.
  change_Z_to_nat. rewrite upd_Znth0.
  rewrite Zlength_cons'.
  rewrite sublist_1_cons.
  replace (Zlength l + 1 - 1) with (Zlength l) by omega.
  orewrite (@sublist_same A).
  reflexivity.
  clear i Hi ; intros i Hi iHi l v.
  destruct l ; replace (Z.to_nat (Z.succ i)) with (S (Z.to_nat i)) by (rewrite Z2Nat.inj_succ ; go);
  change (Z.succ i) with (i + 1).
  unfold upd_Znth ; unfold sublist ; repeat rewrite skipn_nil ; repeat rewrite firstn_nil ; go.
  simpl ; rewrite <- iHi.
  unfold upd_Znth.
  unfold sublist ; change_Z_to_nat.
  repeat rewrite skipn_0.
  replace (Z.to_nat (i + 1 - 0)) with (S (Z.to_nat (i))).
  replace (Z.to_nat (i - 0)) with (Z.to_nat (i)).
  simpl.
  f_equal.
  f_equal.
  f_equal.
  f_equal.
  f_equal.
  rewrite Zlength_cons' ; omega.
  replace (Z.to_nat (i + 1 + 1)) with (S (Z.to_nat (i + 1))).
  go.
  rewrite <- Z2Nat.inj_succ ; go.
  f_equal ; go.
  rewrite <- Z2Nat.inj_succ ; go.
  f_equal ; go.
Qed.

Lemma upd_Znth_cons: forall A (d h:A)  (q:list A), upd_Znth 0 (h::q) d = d :: q.
Proof. intros. orewrite upd_Znth_upd_nth. reflexivity. Qed.

Lemma upd_Znth_list_alter: forall A (f : A -> A) (i:Z) (v:A) (l: list A), 0 <= i -> f = (fun x => v) -> 
i < Zlength l -> upd_Znth i l v = list.list_alter f (Z.to_nat i) l.
Proof. intros. orewrite upd_Znth_upd_nth. apply upd_nth_list_alter.
assumption.
apply Z2Nat.inj_lt in H1.
rewrite Zlength_correct in H1.
rewrite Nat2Z.id in H1.
assumption.
omega.
apply Zlength_pos.
Qed.

Lemma upd_Znth_alter: forall A (f : A -> A) (i:Z) (v:A) (l: list A), 0 <= i -> f = (fun x => v) -> 
i < Zlength l -> upd_Znth i l v = base.alter f (Z.to_nat i) l.
Proof.
unfold base.alter.
apply upd_Znth_list_alter.
Qed.

Lemma upd_Znth_comm_n: forall A i j (l:list A) ni nj, (Z.of_nat i) < Zlength l -> (Z.of_nat j) < Zlength l -> (Z.of_nat i) <> (Z.of_nat j) ->  upd_Znth (Z.of_nat i) (upd_Znth (Z.of_nat j) l nj) ni = upd_Znth (Z.of_nat j) (upd_Znth (Z.of_nat i) l ni) nj.
Proof.
 intros. rewrite ?upd_Znth_upd_nth ; try omega.
apply upd_nth_comm;rewrite ?Nat2Z.id ; try omega ; [move: H | move: H0] ; rewrite Zlength_correct; apply Nat2Z.inj_lt.
Qed.

Lemma upd_Znth_comm: forall A i j (l:list A) ni nj, 0 <= i -> i < Zlength l -> 0 <= j -> j < Zlength l -> i <> j ->  upd_Znth i (upd_Znth j l nj) ni = upd_Znth j (upd_Znth i l ni) nj.
Proof.
  intros.
  assert(Hi: exists (i':nat), Z.of_nat i' = i).
    exists (nat_of_Z i); apply Coqlib.nat_of_Z_eq; omega.
  assert(Hj: exists (j':nat), Z.of_nat j' = j).
    exists (nat_of_Z j); apply Coqlib.nat_of_Z_eq; omega.
  destruct Hi as [i' Hi].
  destruct Hj as [j' Hj].
  rewrite -Hi -Hj.
  apply upd_Znth_comm_n;
  rewrite ?Hi ?Hj //.
Qed.

Lemma Znth_nth : forall A (i:Z) (d:A) (l:list A), 0 <= i -> Znth i l d = nth (nat_of_Z i) l d.
Proof.
  induction i ; go.
  intros.
  assert(H':= Pos2Z.neg_is_neg p).
  omega.
Qed.

Ltac convert_power_to_Z := 
    change (two_p 16) with 65536 in *;
    change (2^8) with (256) in *;
    change Int.max_unsigned with (4294967295) in *;
    change Int.max_signed with (2147483647) in *;
    change Int.min_signed with (-2147483648) in *;
    change Byte.max_unsigned with (255) in *;
    change (2^16) with 65536 in *;
    change (-2^16) with (-65536) in *;
    change (2^26) with 67108864 in *;
    change (-2^26) with (-67108864) in *;
    change (2^47) with 140737488355328 in *;
    change (-2^62) with (-4611686018427387904) in *;
    change (2^62) with (4611686018427387904) in *;
    change (-2^63) with (-9223372036854775808) in *;
    change (2^63) with (9223372036854775808) in *;
    change Int64.min_signed with (-9223372036854775808) in *;
    change Int64.max_signed with (9223372036854775807) in *;
    change Int64.max_unsigned with (18446744073709551615) in *.

Ltac solve_bounds_by_values := 
  convert_power_to_Z; simpl ; try omega.

Lemma simple_S_i: forall i , 0 <= i -> nat_of_Z (i + 1) = S (nat_of_Z i).
Proof.
  intros.
  orewrite nat_of_Z_plus.
  change (nat_of_Z 1) with 1%nat ; omega.
Qed.

Definition tkdp A (i:Z) (a b:list A) := firstn (nat_of_Z i) a ++ skipn (nat_of_Z i) b.
Arguments tkdp [A] _ _ _.

Lemma tkdp_all : forall A (a b:list A),
  Zlength a = Zlength b ->
  tkdp (Zlength a) a b = a.
Proof.
intros A a b.
rewrite /tkdp ?Zlength_correct /nat_of_Z => Hab.
rewrite {2}Hab ?Nat2Z.id firstn_all list.drop_all app_nil_r ; reflexivity.
Qed.

Lemma Znth_tkdp : forall A (a b: list A) (d:A) i,
  0 <= i <= Zlength a ->
  Znth i (tkdp i a b) d = Znth i b d.
Proof.
  intros A a b d i Hia.
  rewrite /tkdp app_Znth2 Zlength_firstn Z.min_l ?Z.max_r ?Znth_skipn.
  replace (i - i + i) with i ; try reflexivity.
  all: omega.
Qed.

Lemma tkdp_Zlength : forall A (a b: list A),
  Zlength a = Zlength b ->
  forall i, Zlength (tkdp i a b) = Zlength a.
Proof.
  intros.
  rewrite /tkdp; apply take_drop_Zlength; assumption.
Qed.

Lemma upd_Znth_app_step_length:
  forall {A} i (a r:list A) d, 
    0 <= i ->
    (nat_of_Z i < Datatypes.length r)%nat ->
    (nat_of_Z i < Datatypes.length a)%nat ->
    firstn (S (nat_of_Z i)) a ++ skipn (S (nat_of_Z i)) r =
    upd_Znth i (firstn (nat_of_Z i) a ++ skipn (nat_of_Z i) r) (Znth i a d).
Proof.
  intros.
  rewrite (nth_drop (nat_of_Z i) _ d); try assumption.
  rewrite list.cons_middle;rewrite app_assoc ; rewrite upd_Znth_app1.

  2:{
  rewrite Zlength_app ; do 2 rewrite Zlength_correct ; 
  orewrite firstn_length_le ; rewrite Z2Nat.id ; simpl; omega.
  }
  rewrite upd_Znth_app2.

  2:{
  rewrite Zlength_correct.
  orewrite firstn_length_le.
  orewrite Z2Nat.id.
  rewrite Zlength_cons Zlength_nil.
  omega.
  }

  replace (i - Zlength (firstn (nat_of_Z i) a)) with 0.

  2:{
  rewrite Zlength_correct.
  orewrite firstn_length_le.
  orewrite Z2Nat.id.
  }

  rewrite upd_Znth_cons.
  f_equal.
  rewrite <- (list.take_drop (nat_of_Z i) a).
  oreplace (S (nat_of_Z i)) ((nat_of_Z i) + 1)%nat.
  rewrite list.take_plus_app. 2: (rewrite firstn_length_le; omega).
  rewrite (list.take_drop (nat_of_Z i) a).
  f_equal.
  rewrite <- (firstn_1_skipn _ _ d) by assumption.
  orewrite Znth_nth.
  reflexivity.
Qed.

Lemma upd_Znth_app_step_Zlength:
  forall {A} i (a r:list A) d, 
    0 <= i ->
    i < Zlength r ->
    i < Zlength a ->
    firstn (S (Z.to_nat i)) a ++ skipn (S (Z.to_nat i)) r =
    upd_Znth i (firstn (Z.to_nat i) a ++ skipn (Z.to_nat i) r) (Znth i a d).
Proof.
intros A i a r d Hi. rewrite ?Zlength_correct => Hr Ha ; apply upd_Znth_app_step_length ; try  omega;
apply Nat2Z.inj_lt ; rewrite /nat_of_Z Z2Nat.id ; try omega.
Qed.

Ltac solve_bounds_by_values_Forall := 
    try rewrite Int64.signed_repr; try reflexivity;
    try rewrite <- Znth_nth by omega;
    apply Forall_Znth; go ;
    eapply (@Forall_impl _ (fun x : ℤ => - 2 ^ 62 < x < 2 ^ 62));
    try assumption ;
    let Hx := fresh in intros ? Hx ;
    convert_power_to_Z; omega.

Ltac solve_bounds_by_values_Forall_impl :=
  eapply list.Forall_impl ; eauto;
  let Hx := fresh in intros ? Hx ;
  convert_power_to_Z ; simpl in Hx; simpl ; omega.

Ltac solve_bounds_by_values_Znth := 
    try rewrite Int64.signed_repr; try reflexivity;
    apply Forall_Znth; go ;
    eapply Forall_impl ; eauto;
    let Hx := fresh in intros ? Hx ;
    simpl in Hx;
    solve_bounds_by_values.

Ltac solve_bounds_by_values_ H := 
    try rewrite Int64.signed_repr; try reflexivity;
    apply Forall_Znth; try rewrite H; go ;
    eapply list.Forall_impl ; eauto;
    let Hx := fresh in intros ? Hx ;
    simpl in Hx;
    solve_bounds_by_values.

Ltac solve_bounds_by_values_f f :=
    try rewrite Int64.signed_repr; 
    try rewrite Int.signed_repr; 
    try rewrite Int.unsigned_repr; 
    try reflexivity;
    apply Forall_Znth; go ;
    eapply (@Forall_impl _ f);
    try assumption ;
    let Hx := fresh in intros ? Hx ;
    solve_bounds_by_values.

Ltac prove_bounds_access_array :=
  rewrite Zlength_map ; go.

Ltac prove_access_array :=
  go_lowerx ; entailer!;
  repeat rewrite (Znth_map Int64.zero); auto;
  prove_bounds_access_array.

Ltac prove_exists_aux_from_array :=
  erewrite Znth_map ; eexists ; try reflexivity ; prove_bounds_access_array.

Ltac inequality_sum_Zlength :=
  match goal with
    | [ |- ?i <= ?i <= ?i + Zlength ?l ] => assert(0 <= Zlength l) by apply Zlength_pos ; omega
  end.

Definition undef16 := list_repeat (Z.to_nat 16) Vundef.
Definition undef31 := list_repeat (Z.to_nat 31) Vundef.
Definition undef32 := list_repeat (Z.to_nat 32) Vundef.
Definition undef80 := list_repeat (Z.to_nat 80) Vundef.

Definition nil16 := list_repeat (Z.to_nat 16) 0.
Definition nil31 := list_repeat (Z.to_nat 31) 0.

Lemma nil16_nul16 : nil16 = Low.C_0. Proof. reflexivity. Qed.
Lemma undef16_length : (length undef16 = 16)%nat. Proof. go. Qed.
Lemma undef16_Zlength : Zlength undef16 = 16. Proof. go. Qed.
Lemma undef31_length : (length undef31 = 31)%nat. Proof. go. Qed.
Lemma undef31_Zlength : Zlength undef31 = 31. Proof. go. Qed.
Lemma undef32_length : (length undef32 = 32)%nat. Proof. go. Qed.
Lemma undef32_Zlength : Zlength undef32 = 32. Proof. go. Qed.
Lemma undef80_length : (length undef80 = 80)%nat. Proof. go. Qed.
Lemma undef80_Zlength : Zlength undef80 = 80. Proof. go. Qed.
Lemma nil16_length : (length nil16 = 16)%nat. Proof. go. Qed.
Lemma nil16_Zlength : Zlength nil16 = 16. Proof. go. Qed.
Lemma nil31_length : (length nil31 = 31)%nat. Proof. go. Qed.
Lemma nil31_Zlength : Zlength nil31 = 31. Proof. go. Qed.

Close Scope Z.