Require Import stdpp.prelude.
From Tweetnacl Require Import Libs.LibTactics.
From Tweetnacl Require Import Libs.LibTactics_SF.
Require Import mathcomp.ssreflect.ssreflect.

Section nth_f.
Context {I} {O} (f:I -> O) (v:I).

Fixpoint nth_f (n:nat) (x:list I) {struct x} : O := match n,x with 
  | _, [] => f v
  | 0 , h :: q => f h
  | S n, h :: q => nth_f n q
end.

Lemma nth_f_ext: forall n x,
  f (nth n x v) = nth_f n x.
Proof.
  move=> n l; gen n ; induction l ; destruct n ; simpl ; auto.
Qed.
End nth_f.

Lemma ListSame : forall A (h1 h2: A) (q1 q2:list A), h1 :: q1 = h2 :: q2 <-> h1 = h2 /\ q1 = q2.
Proof. boum. Qed.

Lemma nth_drop : forall A (n:nat) (l:list A) (d: A), n < length l -> drop n l = nth n l d :: drop (S n) l.
Proof. induction n ; destr_boum l. Qed.
Arguments nth_drop [A] _ _ _ _.

Lemma take_drop_length: forall A (n:nat) (l l':list A),
  length l = length l' -> length (take n l ++ drop n l') = length l.
Proof. move => A n l l' Hll'.
have H: n < length l \/ length l <= n by omega.
destruct H ; rewrite app_length drop_length -Hll' ; [rewrite take_length_le|rewrite take_length_ge] ; omega.
Qed.
Arguments take_drop_length [A] _ _ _.

Lemma take_drop_Zlength: forall A (n:nat) (l l':list A),
  Zlength l = Zlength l' -> Zlength (take n l ++ drop n l') = Zlength l.
Proof. convert_length_to_Zlength take_drop_length. Qed.
Arguments take_drop_Zlength [A] _ _ _.

Lemma nth_take: forall A (n:nat) (l l':list A) d,
  n <= length l -> nth n ((take n l) ++ l') d = nth 0 l' d.
Proof. induction n ; destr_boum l. Qed.
Arguments nth_take [A] _ _ _ _ _.

Lemma nth_take_full: forall A (n m:nat) (l:list A) d,
  n < m -> nth n (take m l) d = nth n l d.
Proof. induction n ; destruct m; destr_boum l. Qed.
Arguments nth_take_full [A] _ _ _ _.

Lemma take_cons: forall A (n:nat) (l:list A) d,
  n < length l -> (take n l) ++ nth n l d :: nil = take (S n) l.
Proof. induction n ; destr_boum l ; simpl in * ; f_equal ; apply IHn ; omega. Qed.
Arguments take_cons [A] _ _ _ _.

Lemma nth_drop_2 : forall A (n:nat) (l:list A) (d:A), n <= length l -> nth n l d = nth 0 (drop n l) d.
Proof. induction n ; destr_boum l. Qed.
Arguments nth_drop [A] _ _ _.

Fixpoint upd_nth {A} (n:nat) (l:list A) (v:A) := match l with
  | [] => match n with
    | 0%nat => v :: []
    | S p => v :: []
    end
  | h :: q => match n with
    | 0%nat => v :: q
    | S p => h :: (upd_nth p q v)
    end
  end.

Lemma upd_nth_length:
  forall (A : Type) (i : nat) (l : list A) (v : A),
  0 <= i < length l -> length (upd_nth i l v) = length l.
Proof. induction i ; destruct l; simpl ;
  repeat match goal with
  | _ => progress intros
  | _ => reflexivity
  | _ => omega
  | [ H : _ < 0 |- _ ] => inversion H
  | [ H : _ ≤ _ ∧ _ < _ |- _] => inv H
  | [ |- S _ = S _ ] => f_equal ; apply IHi
  | [ H : S _ < S _ |-  _] => inv H
  end.
Qed.


Lemma upd_nth_map:
  forall (A B : Type) (f : A -> B) (i : nat) (l : list A) (v : A),
  upd_nth i (map f l) (f v) = map f (upd_nth i l v).
Proof. induction i ; destruct l; simpl ; intros ;
repeat match goal with
  | _ => progress intros
  | _ => reflexivity
  | _ => omega
  | _ => rewrite IHi
  end.
Qed.

Lemma upd_nth_lookup:
  forall (K : nat) (A : Type) (l : list A),
  length l = K ->
  forall (i j : nat) (d v : A),
  0 <= i < K ->
  0 <= j < K ->
  i = j /\ nth i (upd_nth j l v) d = v \/
  i <> j /\ nth i (upd_nth j l v) d = nth i l d.
Proof.
  move => K A l; move: K. induction l; intros [] HSl i j d v HSi HSj;
  simpl in HSl ; try omega.
  inversion HSl as [Hl].
  destruct i, j ; [left | right | right| ] ; go =>  /=.
  have Hi : 0 ≤ i ∧ i < n by omega.
  have Hj : 0 ≤ j ∧ j < n by omega.
  clear HSi HSj HSl.
  apply (IHl n Hl i j d v) in Hj.
  2: assumption.
  destruct Hj as [Hj|Hj]; [left|right]; destruct Hj ; go.
Qed.

Lemma upd_nth_lookup':
  forall (K : nat) (A : Type) (l : list A),
  length l = K ->
  forall (i : nat),
  0 <= i < K ->
  forall (j : nat),
  0 <= j < K ->
  forall d v : A,
  nth i (upd_nth j l v) d = (if beq_nat i j then v else nth i l d).
Proof.
  move => K A l Hl i Hi j H d v.
  apply (upd_nth_lookup K A l Hl i j d v Hi) in H.
  destruct H as [H|H];
  destruct H as [Hij Hnth].
  subst i;
  flatten.
  apply beq_nat_false in Eq; tryfalse.
  flatten.
  apply beq_nat_true in Eq ; tryfalse.
Qed.

Lemma upd_nth_same:
  forall (A : Type) (i : nat) (l : list A) (u d : A),
  0 <= i < length l -> nth i (upd_nth i l u) d = u.
Proof.
induction i ; destruct l; simpl  ; intros ;
repeat match goal with
  | _ => progress intros
  | _ => reflexivity
  | _ => omega
  | _ => rewrite IHi
  end.
Qed.

Lemma upd_nth_diff:
  forall (A : Type) (i j : nat) (l : list A) (u d : A),
  0 <= i < length l ->
  0 <= j < length l -> i <> j -> nth i (upd_nth j l u) d = nth i l d.
Proof.
  intros A i j l; gen i j ; induction l ; intros [] [] d v HSi HSj Hij;
  simpl in * ; go.
Qed.

Lemma upd_nth_app1:
  forall (A : Type) (i : nat) (l1 l2 : list A),
  0 <= i < length l1 ->
  forall v : A, upd_nth i (l1 ++ l2) v = upd_nth i l1 v ++ l2.
Proof.
  intros A i l1; gen i; induction l1 ; intros [] l2 HSi v;
  simpl in * ; go.
  f_equal ; go.
Qed.

Lemma upd_nth_app2:
  forall (A : Type) (l1 l2 : list A) (i : nat) (v : A),
  length l1 <= i <= length l1 + length l2 ->
  upd_nth i (l1 ++ l2) v = l1 ++ upd_nth (i - length l1) l2 v.
Proof.
  induction l1 ; intros l2 [] v Hl1 ; simpl in * ; try reflexivity.
  omega.
  have Hl1': length l1 ≤ n ∧ n ≤ length l1 + length l2 by omega.
  apply (IHl1 l2 n v) in Hl1'.
  go.
Qed.

Lemma upd_nth0:
  forall (A : Type) (l : list A) (h v : A),
  upd_nth 0 (h::l) v = v :: l.
Proof. reflexivity. Qed.

Lemma upd_nth_take_small: 
  forall (A : Type) (n m:nat) (l : list A) (v : A),
  n < length l ->
  n <= m ->
  take n (upd_nth m l v) = take n l.
Proof.
   induction n ; intros [|m] [|h l] v Hnl Hnm ; simpl in Hnl ; try reflexivity ; try omega.
   simpl.
   fequals.
   apply IHn ; omega.
Qed.

Lemma upd_nth_app':
  forall (A : Type) (n : nat) (l1 : list A) (v : A) (l2 : list A) (w : A),
  length l1 = n -> upd_nth n (l1 ++ v :: l2) w = l1 ++ w :: l2.
Proof.
  intros.
  rewrite upd_nth_app2.
  2: by omega.
  by oreplace (n - length l1) 0.
Qed.

Lemma upd_nth_list_alter: forall A (f : A -> A) i (v:A) (l: list A), f = (fun x => v) -> 
i < length l -> upd_nth i l v = list_alter f i l.
Proof.
intros A f; induction i as [| i IHi]; intros v l Hf H.
intros. destruct l. simpl in H. omega.
unfold upd_nth.
simpl.
rewrite Hf.
reflexivity.
destruct l ; simpl in H.
inversion H.
change (a::l) with ([a] ++ l).
rewrite upd_nth_app2 ; simpl.
rewrite -minus_n_O.
f_equal.
go.
omega.
Qed.

Lemma upd_nth_alter: forall A (f : A -> A) (i: nat) (v:A) (l: list A), 0 <= i -> f = (fun x => v) -> 
i < length l -> upd_nth i l v = alter f i l.
Proof.  intros ; unfold base.alter ; apply upd_nth_list_alter ; auto. Qed.

Lemma upd_nth_app_step:
  forall i (a r:list Z) d, 
    0 <= i ->
    i < length r ->
    i < length a ->
    firstn (S i) a ++ skipn (S i) r =
    upd_nth i (firstn i a ++ skipn i r) (nth i a d).
Proof.
  intros.
  rewrite (nth_drop i r 0).
  rewrite cons_middle app_assoc upd_nth_app1.
  2: rewrite app_length firstn_length_le ; go.
  rewrite upd_nth_app2.
  2: rewrite firstn_length_le ; simpl; omega.
  replace (i - length (firstn i a)) with 0.
  2: rewrite firstn_length_le; omega.
  rewrite upd_nth0.
  f_equal_fixed.
  rewrite -(take_drop i a).
  oreplace (S i) (i + 1)%nat.
  rewrite take_plus_app.
  rewrite (take_drop i a).
  2: (rewrite firstn_length_le; omega).
  f_equal.
  clear H0 r.
  gen i.
  induction a ; intros [] Hi Hl ; go.
  done.
Qed.

Definition list_ind_by_2 :
    forall A (P : list A → Prop),
    P [] →
    (forall a, P [a]) →
    (forall (a b:A) (l : list A), P l → P (a :: b :: l)) →
    forall (l : list A), P l :=
       fun A => fun P => fun P0 => fun P1 => fun PSS =>
          fix f (l : list A) := match l with
                             [] => P0
                           | [a] => P1 a
                           | a :: b :: l => PSS a b l (f l)
                          end.


Lemma upd_nth_comm: forall A i j (l:list A) ni nj, i < length l -> j < length l -> i <> j ->  upd_nth i (upd_nth j l nj) ni = upd_nth j (upd_nth i l ni) nj.
Proof.
  induction i.
  destruct j; intros.
  tryfalse.
  destruct l.
  simpl in H0 ; omega.
  reflexivity.
  intros.
  destruct l.
  simpl in H ; omega.
  destruct j.
  reflexivity.
  simpl.
  f_equal_fixed.
  apply IHi.
  move: H ; simpl; apply lt_S_n.
  move: H0 ; simpl; apply lt_S_n.
  intros H'.
  apply H1; subst; trivial.
Qed.

Lemma upd_nth_upd_nth: forall A i (l:list A) ni nj, i < length l -> upd_nth i (upd_nth i l nj) ni = upd_nth i l ni.
Proof.
  induction i; intros.
  destruct l.
  simpl in H ; omega.
  reflexivity.
  destruct l.
  simpl in H ; omega.
  simpl.
  f_equal.
  apply IHi.
  move: H ; simpl; apply lt_S_n.
Qed.

Lemma length_pos : forall (A:Type) (l:list A), 0 <= length l.
Proof. boum. Qed.

Lemma map_drop : forall A B (f: A -> B) (l:list A) n, map f (drop n l) = drop n (map f l).
Proof. intros A B f ; induction l ; destruct n ; go. Qed.

Open Scope Z.

Lemma Zlength_pos: forall {A : Type} (l:list A), 0 <= Zlength l.
Proof. intros ; rewrite Zlength_correct ; go. Qed.

Lemma app_Zlength: forall {A : Type} (l l' : list A), Zlength (l ++ l') = Zlength l + Zlength l'.
Proof. intros; by rewrite !Zlength_correct -Nat2Z.inj_add app_length. Qed.

Lemma Zlength_cons' : forall {A : Type} (x : A) (l : list A), Zlength (x :: l) = (Zlength l) + 1.
Proof. intros ; by rewrite Zlength_cons. Qed.

Lemma Zlength_map: forall A B (f: A -> B) l, Zlength (map f l) = Zlength l.
Proof. intros; induction l ; auto ; rewrite map_cons !Zlength_cons ; go. Qed.

Lemma upd_nth_Zlength:
  forall (A : Type) (i : nat) (l : list A) (v : A),
  0 <= i < Zlength l -> Zlength (upd_nth i l v) = Zlength l.
Proof. convert_length_to_Zlength upd_nth_length. Qed.

Lemma upd_nth_same_Zlength:
  forall (A : Type) (i : nat) (l : list A) (u d : A),
  0 <= i < Zlength l -> nth i (upd_nth i l u) d = u.
Proof. convert_length_to_Zlength upd_nth_same. Qed.

Lemma upd_nth_diff_Zlength:
  forall (A : Type) (i j : nat) (l : list A) (u d : A),
  0 <= i < Zlength l ->
  0 <= j < Zlength l -> i <> j -> nth i (upd_nth j l u) d = nth i l d.
Proof. convert_length_to_Zlength upd_nth_diff. Qed.

Lemma upd_nth_upd_nth_Zlength : forall A (i:nat) (l:list A) ni nj, i < Zlength l -> upd_nth i (upd_nth i l nj) ni = upd_nth i l ni.
Proof. convert_length_to_Zlength upd_nth_upd_nth. Qed.

Lemma upd_nth_comm_Zlength : forall A (i j:nat) (l:list A) ni nj, i < Zlength l -> j < Zlength l -> i <> j ->  upd_nth i (upd_nth j l nj) ni = upd_nth j (upd_nth i l ni) nj.
Proof. convert_length_to_Zlength upd_nth_comm. Qed.

Lemma upd_nth_take_small_Zlength:
  forall (A : Type) (n m:nat) (l : list A) (v : A),
  n < Zlength l ->
  n <= m ->
  take n (upd_nth m l v) = take n l.
Proof. convert_length_to_Zlength upd_nth_take_small. Qed.

Lemma take_cons_Zlength: forall A n (l:list A) d,
  0 <= n < Zlength l -> (take (Z.to_nat n) l) ++ nth (Z.to_nat n) l d :: nil = take (Z.to_nat (n + 1)) l.
Proof. intros. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)).
rapply take_cons.
(* apply take_cons. *)
rewrite Zlength_correct in H.
apply Nat2Z.inj_lt.
rewrite Z2Nat.id ; omega.
rewrite Z2Nat.inj_add.
change (Z.to_nat 1) with 1%nat.
all: omega.
Qed.
Arguments take_cons_Zlength [A] _ _ _ _.

Lemma upd_nth_list_alter_Zlength: forall A (f : A -> A) (i:nat) (v:A) (l: list A), f = (fun x => v) -> 
i < Zlength l -> upd_nth i l v = list_alter f i l.
Proof. convert_length_to_Zlength upd_nth_list_alter. Qed.

Lemma upd_nth_alter_Zlength: forall A (f : A -> A) (i: nat) (v:A) (l: list A), 0 <= i -> f = (fun x => v) -> 
i < Zlength l -> upd_nth i l v = alter f i l.
Proof. convert_length_to_Zlength upd_nth_alter. Qed.

Close Scope Z.