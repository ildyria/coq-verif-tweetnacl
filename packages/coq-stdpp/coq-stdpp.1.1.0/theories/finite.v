(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Export countable vector.
Set Default Proof Using "Type".

Class Finite A `{EqDecision A} := {
  enum : list A;
  NoDup_enum : NoDup enum;
  elem_of_enum x : x ∈ enum
}.
Hint Mode Finite ! - : typeclass_instances.
Arguments enum : clear implicits.
Arguments enum _ {_ _} : assert.
Arguments NoDup_enum : clear implicits.
Arguments NoDup_enum _ {_ _} : assert.
Definition card A `{Finite A} := length (enum A).

Program Definition finite_countable `{Finite A} : Countable A := {|
  encode := λ x,
    Pos.of_nat $ S $ from_option id 0 $ fst <$> list_find (x =) (enum A);
  decode := λ p, enum A !! pred (Pos.to_nat p)
|}.
Arguments Pos.of_nat : simpl never.
Next Obligation.
  intros ?? [xs Hxs HA] x; unfold encode, decode; simpl.
  destruct (list_find_elem_of (x =) xs x) as [[i y] Hi]; auto.
  rewrite Nat2Pos.id by done; simpl; rewrite Hi; simpl.
  destruct (list_find_Some (x =) xs i y); naive_solver.
Qed.
Hint Immediate finite_countable : typeclass_instances.

Definition find `{Finite A} P `{∀ x, Decision (P x)} : option A :=
  list_find P (enum A) ≫= decode_nat ∘ fst.

Lemma encode_lt_card `{finA: Finite A} x : encode_nat x < card A.
Proof.
  destruct finA as [xs Hxs HA]; unfold encode_nat, encode, card; simpl.
  rewrite Nat2Pos.id by done; simpl.
  destruct (list_find _ xs) as [[i y]|] eqn:?; simpl.
  - destruct (list_find_Some (x =) xs i y); eauto using lookup_lt_Some.
  - destruct xs; simpl. exfalso; eapply not_elem_of_nil, (HA x). lia.
Qed.
Lemma encode_decode A `{finA: Finite A} i :
  i < card A → ∃ x, decode_nat i = Some x ∧ encode_nat x = i.
Proof.
  destruct finA as [xs Hxs HA].
  unfold encode_nat, decode_nat, encode, decode, card; simpl.
  intros Hi. apply lookup_lt_is_Some in Hi. destruct Hi as [x Hx].
  exists x. rewrite !Nat2Pos.id by done; simpl.
  destruct (list_find_elem_of (x =) xs x) as [[j y] Hj]; auto.
  destruct (list_find_Some (x =) xs j y) as [? ->]; auto.
  rewrite Hj; csimpl; eauto using NoDup_lookup.
Qed.
Lemma find_Some `{finA: Finite A} P `{∀ x, Decision (P x)} x :
  find P = Some x → P x.
Proof.
  destruct finA as [xs Hxs HA]; unfold find, decode_nat, decode; simpl.
  intros Hx. destruct (list_find _ _) as [[i y]|] eqn:Hi; simplify_eq/=.
  rewrite !Nat2Pos.id in Hx by done.
  destruct (list_find_Some P xs i y); naive_solver.
Qed.
Lemma find_is_Some `{finA: Finite A} P `{∀ x, Decision (P x)} x :
  P x → ∃ y, find P = Some y ∧ P y.
Proof.
  destruct finA as [xs Hxs HA]; unfold find, decode; simpl.
  intros Hx. destruct (list_find_elem_of P xs x) as [[i y] Hi]; auto.
  rewrite Hi. destruct (list_find_Some P xs i y); simplify_eq/=; auto.
  exists y. by rewrite !Nat2Pos.id by done.
Qed.

Definition encode_fin `{Finite A} (x : A) : fin (card A) :=
  Fin.of_nat_lt (encode_lt_card x).
Program Definition decode_fin `{Finite A} (i : fin (card A)) : A :=
  match Some_dec (decode_nat i) return _ with
  | inleft (x ↾ _) => x | inright _ => _
  end.
Next Obligation.
  intros A ?? i ?; exfalso.
  destruct (encode_decode A i); naive_solver auto using fin_to_nat_lt.
Qed.
Lemma decode_encode_fin `{Finite A} (x : A) : decode_fin (encode_fin x) = x.
Proof.
  unfold decode_fin, encode_fin. destruct (Some_dec _) as [[x' Hx]|Hx].
  { by rewrite fin_to_of_nat, decode_encode_nat in Hx; simplify_eq. }
  exfalso; by rewrite ->fin_to_of_nat, decode_encode_nat in Hx.
Qed.

Lemma fin_choice {n} {B : fin n → Type} (P : ∀ i, B i → Prop) :
  (∀ i, ∃ y, P i y) → ∃ f, ∀ i, P i (f i).
Proof.
  induction n as [|n IH]; intros Hex.
  { exists (fin_0_inv _); intros i; inv_fin i. }
  destruct (IH _ _ (λ i, Hex (FS i))) as [f Hf], (Hex 0%fin) as [y Hy].
  exists (fin_S_inv _ y f); intros i; by inv_fin i.
Qed.
Lemma finite_choice `{Finite A} {B : A → Type} (P : ∀ x, B x → Prop) :
  (∀ x, ∃ y, P x y) → ∃ f, ∀ x, P x (f x).
Proof.
  intros Hex. destruct (fin_choice _ (λ i, Hex (decode_fin i))) as [f ?].
  exists (λ x, eq_rect _ _ (f(encode_fin x)) _ (decode_encode_fin x)); intros x.
  destruct (decode_encode_fin x); simpl; auto.
Qed.

Lemma card_0_inv P `{finA: Finite A} : card A = 0 → A → P.
Proof.
  intros ? x. destruct finA as [[|??] ??]; simplify_eq.
  by destruct (not_elem_of_nil x).
Qed.
Lemma finite_inhabited A `{finA: Finite A} : 0 < card A → Inhabited A.
Proof.
  unfold card; intros. destruct finA as [[|x ?] ??]; simpl in *; [exfalso;lia|].
  constructor; exact x.
Qed.
Lemma finite_inj_submseteq `{finA: Finite A} `{finB: Finite B} (f: A → B)
  `{!Inj (=) (=) f} : f <$> enum A ⊆+ enum B.
Proof.
  intros. destruct finA, finB. apply NoDup_submseteq; auto using NoDup_fmap_2.
Qed.
Lemma finite_inj_Permutation `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} : card A = card B → f <$> enum A ≡ₚ enum B.
Proof.
  intros. apply submseteq_Permutation_length_eq.
  - by rewrite fmap_length.
  - by apply finite_inj_submseteq.
Qed.
Lemma finite_inj_surj `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} : card A = card B → Surj (=) f.
Proof.
  intros HAB y. destruct (elem_of_list_fmap_2 f (enum A) y) as (x&?&?); eauto.
  rewrite finite_inj_Permutation; auto using elem_of_enum.
Qed.

Lemma finite_surj A `{Finite A} B `{Finite B} :
  0 < card A ≤ card B → ∃ g : B → A, Surj (=) g.
Proof.
  intros [??]. destruct (finite_inhabited A) as [x']; auto with lia.
  exists (λ y : B, from_option id x' (decode_nat (encode_nat y))).
  intros x. destruct (encode_decode B (encode_nat x)) as (y&Hy1&Hy2).
  { pose proof (encode_lt_card x); lia. }
  exists y. by rewrite Hy2, decode_encode_nat.
Qed.
Lemma finite_inj A `{Finite A} B `{Finite B} :
  card A ≤ card B ↔ ∃ f : A → B, Inj (=) (=) f.
Proof.
  split.
  - intros. destruct (decide (card A = 0)) as [HA|?].
    { exists (card_0_inv B HA). intros y. apply (card_0_inv _ HA y). }
    destruct (finite_surj A B) as (g&?); auto with lia.
    destruct (surj_cancel g) as (f&?). exists f. apply cancel_inj.
  - intros [f ?]. unfold card. rewrite <-(fmap_length f).
    by apply submseteq_length, (finite_inj_submseteq f).
Qed.
Lemma finite_bijective A `{Finite A} B `{Finite B} :
  card A = card B ↔ ∃ f : A → B, Inj (=) (=) f ∧ Surj (=) f.
Proof.
  split.
  - intros; destruct (proj1 (finite_inj A B)) as [f ?]; auto with lia.
    exists f; auto using (finite_inj_surj f).
  - intros (f&?&?). apply (anti_symm (≤)); apply finite_inj.
    + by exists f.
    + destruct (surj_cancel f) as (g&?); eauto using cancel_inj.
Qed.
Lemma inj_card `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} : card A ≤ card B.
Proof. apply finite_inj. eauto. Qed.
Lemma surj_card `{Finite A} `{Finite B} (f : A → B)
  `{!Surj (=) f} : card B ≤ card A.
Proof.
  destruct (surj_cancel f) as (g&?).
  apply inj_card with g, cancel_inj.
Qed.
Lemma bijective_card `{Finite A} `{Finite B} (f : A → B)
  `{!Inj (=) (=) f} `{!Surj (=) f} : card A = card B.
Proof. apply finite_bijective. eauto. Qed.

(** Decidability of quantification over finite types *)
Section forall_exists.
  Context `{Finite A} (P : A → Prop).

  Lemma Forall_finite : Forall P (enum A) ↔ (∀ x, P x).
  Proof. rewrite Forall_forall. intuition auto using elem_of_enum. Qed.
  Lemma Exists_finite : Exists P (enum A) ↔ (∃ x, P x).
  Proof. rewrite Exists_exists. naive_solver eauto using elem_of_enum. Qed.

  Context `{∀ x, Decision (P x)}.

  Global Instance forall_dec: Decision (∀ x, P x).
  Proof using Type*.
   refine (cast_if (decide (Forall P (enum A))));
    abstract by rewrite <-Forall_finite.
  Defined.
  Global Instance exists_dec: Decision (∃ x, P x).
  Proof using Type*.
   refine (cast_if (decide (Exists P (enum A))));
    abstract by rewrite <-Exists_finite.
  Defined.
End forall_exists.

(** Instances *)
Section enc_finite.
  Context `{EqDecision A}.
  Context (to_nat : A → nat) (of_nat : nat → A) (c : nat).
  Context (of_to_nat : ∀ x, of_nat (to_nat x) = x).
  Context (to_nat_c : ∀ x, to_nat x < c).
  Context (to_of_nat : ∀ i, i < c → to_nat (of_nat i) = i).

  Program Instance enc_finite : Finite A := {| enum := of_nat <$> seq 0 c |}.
  Next Obligation.
    apply NoDup_alt. intros i j x. rewrite !list_lookup_fmap. intros Hi Hj.
    destruct (seq _ _ !! i) as [i'|] eqn:Hi',
      (seq _ _ !! j) as [j'|] eqn:Hj'; simplify_eq/=.
    destruct (lookup_seq_inv _ _ _ _ Hi'), (lookup_seq_inv _ _ _ _ Hj'); subst.
    rewrite <-(to_of_nat i), <-(to_of_nat j) by done. by f_equal.
  Qed.
  Next Obligation.
    intros x. rewrite elem_of_list_fmap. exists (to_nat x).
    split; auto. by apply elem_of_list_lookup_2 with (to_nat x), lookup_seq.
  Qed.
  Lemma enc_finite_card : card A = c.
  Proof. unfold card. simpl. by rewrite fmap_length, seq_length. Qed.
End enc_finite.

Section bijective_finite.
  Context `{Finite A, EqDecision B} (f : A → B) (g : B → A).
  Context `{!Inj (=) (=) f, !Cancel (=) f g}.

  Program Instance bijective_finite: Finite B := {| enum := f <$> enum A |}.
  Next Obligation. apply (NoDup_fmap_2 _), NoDup_enum. Qed.
  Next Obligation.
    intros y. rewrite elem_of_list_fmap. eauto using elem_of_enum.
  Qed.
End bijective_finite.

Program Instance option_finite `{Finite A} : Finite (option A) :=
  {| enum := None :: (Some <$> enum A) |}.
Next Obligation.
  constructor.
  - rewrite elem_of_list_fmap. by intros (?&?&?).
  - apply (NoDup_fmap_2 _); auto using NoDup_enum.
Qed.
Next Obligation.
  intros ??? [x|]; [right|left]; auto.
  apply elem_of_list_fmap. eauto using elem_of_enum.
Qed.
Lemma option_cardinality `{Finite A} : card (option A) = S (card A).
Proof. unfold card. simpl. by rewrite fmap_length. Qed.

Program Instance unit_finite : Finite () := {| enum := [tt] |}.
Next Obligation. apply NoDup_singleton. Qed.
Next Obligation. intros []. by apply elem_of_list_singleton. Qed.
Lemma unit_card : card unit = 1.
Proof. done. Qed.

Program Instance bool_finite : Finite bool := {| enum := [true; false] |}.
Next Obligation.
  constructor. by rewrite elem_of_list_singleton. apply NoDup_singleton.
Qed.
Next Obligation. intros [|]. left. right; left. Qed.
Lemma bool_card : card bool = 2.
Proof. done. Qed.

Program Instance sum_finite `{Finite A, Finite B} : Finite (A + B)%type :=
  {| enum := (inl <$> enum A) ++ (inr <$> enum B) |}.
Next Obligation.
  intros. apply NoDup_app; split_and?.
  - apply (NoDup_fmap_2 _). by apply NoDup_enum.
  - intro. rewrite !elem_of_list_fmap. intros (?&?&?) (?&?&?); congruence.
  - apply (NoDup_fmap_2 _). by apply NoDup_enum.
Qed.
Next Obligation.
  intros ?????? [x|y]; rewrite elem_of_app, !elem_of_list_fmap;
    eauto using @elem_of_enum.
Qed.
Lemma sum_card `{Finite A, Finite B} : card (A + B) = card A + card B.
Proof. unfold card. simpl. by rewrite app_length, !fmap_length. Qed.

Program Instance prod_finite `{Finite A, Finite B} : Finite (A * B)%type :=
  {| enum := foldr (λ x, (pair x <$> enum B ++)) [] (enum A) |}.
Next Obligation.
  intros ??????. induction (NoDup_enum A) as [|x xs Hx Hxs IH]; simpl.
  { constructor. }
  apply NoDup_app; split_and?.
  - by apply (NoDup_fmap_2 _), NoDup_enum.
  - intros [? y]. rewrite elem_of_list_fmap. intros (?&?&?); simplify_eq.
    clear IH. induction Hxs as [|x' xs ?? IH]; simpl.
    { rewrite elem_of_nil. tauto. }
    rewrite elem_of_app, elem_of_list_fmap.
    intros [(?&?&?)|?]; simplify_eq.
    + destruct Hx. by left.
    + destruct IH. by intro; destruct Hx; right. auto.
  - done.
Qed.
Next Obligation.
  intros ?????? [x y]. induction (elem_of_enum x); simpl.
  - rewrite elem_of_app, !elem_of_list_fmap. eauto using @elem_of_enum.
  - rewrite elem_of_app; eauto.
Qed.
Lemma prod_card `{Finite A} `{Finite B} : card (A * B) = card A * card B.
Proof.
  unfold card; simpl. induction (enum A); simpl; auto.
  rewrite app_length, fmap_length. auto.
Qed.

Definition list_enum {A} (l : list A) : ∀ n, list { l : list A | length l = n } :=
  fix go n :=
  match n with
  | 0 => [[]↾eq_refl]
  | S n => foldr (λ x, (sig_map (x ::) (λ _ H, f_equal S H) <$> (go n) ++)) [] l
  end.

Program Instance list_finite `{Finite A} n : Finite { l | length l = n } :=
  {| enum := list_enum (enum A) n |}.
Next Obligation.
  intros ????. induction n as [|n IH]; simpl; [apply NoDup_singleton |].
  revert IH. generalize (list_enum (enum A) n). intros l Hl.
  induction (NoDup_enum A) as [|x xs Hx Hxs IH]; simpl; auto; [constructor |].
  apply NoDup_app; split_and?.
  - by apply (NoDup_fmap_2 _).
  - intros [k1 Hk1]. clear Hxs IH. rewrite elem_of_list_fmap.
    intros ([k2 Hk2]&?&?) Hxk2; simplify_eq/=. destruct Hx. revert Hxk2.
    induction xs as [|x' xs IH]; simpl in *; [by rewrite elem_of_nil |].
    rewrite elem_of_app, elem_of_list_fmap, elem_of_cons.
    intros [([??]&?&?)|?]; simplify_eq/=; auto.
  - apply IH.
Qed.
Next Obligation.
  intros ???? [l Hl]. revert l Hl.
  induction n as [|n IH]; intros [|x l] ?; simpl; simplify_eq.
  { apply elem_of_list_singleton. by apply (sig_eq_pi _). }
  revert IH. generalize (list_enum (enum A) n). intros k Hk.
  induction (elem_of_enum x) as [x xs|x xs]; simpl in *.
  - rewrite elem_of_app, elem_of_list_fmap. left. injection Hl. intros Hl'.
    eexists (l↾Hl'). split. by apply (sig_eq_pi _). done.
  - rewrite elem_of_app. eauto.
Qed.

Lemma list_card `{Finite A} n : card { l | length l = n } = card A ^ n.
Proof.
  unfold card; simpl. induction n as [|n IH]; simpl; auto.
  rewrite <-IH. clear IH. generalize (list_enum (enum A) n).
  induction (enum A) as [|x xs IH]; intros l; simpl; auto.
  by rewrite app_length, fmap_length, IH.
Qed.

Fixpoint fin_enum (n : nat) : list (fin n) :=
  match n with 0 => [] | S n => 0%fin :: (FS <$> fin_enum n) end.
Program Instance fin_finite n : Finite (fin n) := {| enum := fin_enum n |}.
Next Obligation.
  intros n. induction n; simpl; constructor.
  - rewrite elem_of_list_fmap. by intros (?&?&?).
  - by apply (NoDup_fmap _).
Qed.
Next Obligation.
  intros n i. induction i as [|n i IH]; simpl;
    rewrite elem_of_cons, ?elem_of_list_fmap; eauto.
Qed.
Lemma fin_card n : card (fin n) = n.
Proof. unfold card; simpl. induction n; simpl; rewrite ?fmap_length; auto. Qed.
