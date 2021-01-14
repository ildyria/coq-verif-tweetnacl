(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From Coq.QArith Require Import QArith_base Qcanon.
From stdpp Require Export list numbers.
Set Default Proof Using "Type".
Local Open Scope positive.

Class Countable A `{EqDecision A} := {
  encode : A → positive;
  decode : positive → option A;
  decode_encode x : decode (encode x) = Some x
}.
Hint Mode Countable ! - : typeclass_instances.
Arguments encode : simpl never.
Arguments decode : simpl never.

Definition encode_nat `{Countable A} (x : A) : nat :=
  pred (Pos.to_nat (encode x)).
Definition decode_nat `{Countable A} (i : nat) : option A :=
  decode (Pos.of_nat (S i)).
Instance encode_inj `{Countable A} : Inj (=) (=) encode.
Proof.
  intros x y Hxy; apply (inj Some).
  by rewrite <-(decode_encode x), Hxy, decode_encode.
Qed.
Instance encode_nat_inj `{Countable A} : Inj (=) (=) encode_nat.
Proof. unfold encode_nat; intros x y Hxy; apply (inj encode); lia. Qed.
Lemma decode_encode_nat `{Countable A} x : decode_nat (encode_nat x) = Some x.
Proof.
  pose proof (Pos2Nat.is_pos (encode x)).
  unfold decode_nat, encode_nat. rewrite Nat.succ_pred by lia.
  by rewrite Pos2Nat.id, decode_encode.
Qed.

(** * Choice principles *)
Section choice.
  Context `{Countable A} (P : A → Prop).

  Inductive choose_step: relation positive :=
    | choose_step_None {p} : decode (A:=A) p = None → choose_step (Psucc p) p
    | choose_step_Some {p} {x : A} :
       decode p = Some x → ¬P x → choose_step (Psucc p) p.
  Lemma choose_step_acc : (∃ x, P x) → Acc choose_step 1%positive.
  Proof.
    intros [x Hx]. cut (∀ i p,
      i ≤ encode x → 1 + encode x = p + i → Acc choose_step p).
    { intros help. by apply (help (encode x)). }
    induction i as [|i IH] using Pos.peano_ind; intros p ??.
    { constructor. intros j. assert (p = encode x) by lia; subst.
      inversion 1 as [? Hd|?? Hd]; subst;
        rewrite decode_encode in Hd; congruence. }
    constructor. intros j.
    inversion 1 as [? Hd|? y Hd]; subst; auto with lia.
  Qed.

  Context `{∀ x, Decision (P x)}.

  Fixpoint choose_go {i} (acc : Acc choose_step i) : A :=
    match Some_dec (decode i) with
    | inleft (x↾Hx) =>
      match decide (P x) with
      | left _ => x | right H => choose_go (Acc_inv acc (choose_step_Some Hx H))
      end
    | inright H => choose_go (Acc_inv acc (choose_step_None H))
    end.
  Fixpoint choose_go_correct {i} (acc : Acc choose_step i) : P (choose_go acc).
  Proof. destruct acc; simpl. repeat case_match; auto. Qed.
  Fixpoint choose_go_pi {i} (acc1 acc2 : Acc choose_step i) :
    choose_go acc1 = choose_go acc2.
  Proof. destruct acc1, acc2; simpl; repeat case_match; auto. Qed.

  Definition choose (H: ∃ x, P x) : A := choose_go (choose_step_acc H).
  Definition choose_correct (H: ∃ x, P x) : P (choose H) := choose_go_correct _.
  Definition choose_pi (H1 H2 : ∃ x, P x) :
    choose H1 = choose H2 := choose_go_pi _ _.
  Definition choice (HA : ∃ x, P x) : { x | P x } := _↾choose_correct HA.
End choice.

Lemma surj_cancel `{Countable A} `{EqDecision B}
  (f : A → B) `{!Surj (=) f} : { g : B → A & Cancel (=) f g }.
Proof.
  exists (λ y, choose (λ x, f x = y) (surj f y)).
  intros y. by rewrite (choose_correct (λ x, f x = y) (surj f y)).
Qed.

(** * Instances *)
(** ** Injection *)
Section inj_countable.
  Context `{Countable A, EqDecision B}.
  Context (f : B → A) (g : A → option B) (fg : ∀ x, g (f x) = Some x).

  Program Instance inj_countable : Countable B :=
    {| encode y := encode (f y); decode p := x ← decode p; g x |}.
  Next Obligation. intros y; simpl; rewrite decode_encode; eauto. Qed.
End inj_countable.

Section inj_countable'.
  Context `{Countable A, EqDecision B}.
  Context (f : B → A) (g : A → B) (fg : ∀ x, g (f x) = x).

  Program Instance inj_countable' : Countable B := inj_countable f (Some ∘ g) _.
  Next Obligation. intros x. by f_equal/=. Qed.
End inj_countable'.

(** ** Unit *)
Program Instance unit_countable : Countable unit :=
  {| encode u := 1; decode p := Some () |}.
Next Obligation. by intros []. Qed.

(** ** Bool *)
Program Instance bool_countable : Countable bool := {|
  encode b := if b then 1 else 2;
  decode p := Some match p return bool with 1 => true | _ => false end
|}.
Next Obligation. by intros []. Qed.

(** ** Option *)
Program Instance option_countable `{Countable A} : Countable (option A) := {|
  encode o := match o with None => 1 | Some x => Pos.succ (encode x) end;
  decode p := if decide (p = 1) then Some None else Some <$> decode (Pos.pred p)
|}.
Next Obligation.
  intros ??? [x|]; simpl; repeat case_decide; auto with lia.
  by rewrite Pos.pred_succ, decode_encode.
Qed.

(** ** Sums *)
Program Instance sum_countable `{Countable A} `{Countable B} :
  Countable (A + B)%type := {|
    encode xy :=
      match xy with inl x => (encode x)~0 | inr y => (encode y)~1 end;
    decode p :=
      match p with
      | 1 => None | p~0 => inl <$> decode p | p~1 => inr <$> decode p
      end
  |}.
Next Obligation. by intros ?????? [x|y]; simpl; rewrite decode_encode. Qed.

(** ** Products *)
Fixpoint prod_encode_fst (p : positive) : positive :=
  match p with
  | 1 => 1
  | p~0 => (prod_encode_fst p)~0~0
  | p~1 => (prod_encode_fst p)~0~1
  end.
Fixpoint prod_encode_snd (p : positive) : positive :=
  match p with
  | 1 => 1~0
  | p~0 => (prod_encode_snd p)~0~0
  | p~1 => (prod_encode_snd p)~1~0
  end.
Fixpoint prod_encode (p q : positive) : positive :=
  match p, q with
  | 1, 1 => 1~1
  | p~0, 1 => (prod_encode_fst p)~1~0
  | p~1, 1 => (prod_encode_fst p)~1~1
  | 1, q~0 => (prod_encode_snd q)~0~1
  | 1, q~1 => (prod_encode_snd q)~1~1
  | p~0, q~0 => (prod_encode p q)~0~0
  | p~0, q~1 => (prod_encode p q)~1~0
  | p~1, q~0 => (prod_encode p q)~0~1
  | p~1, q~1 => (prod_encode p q)~1~1
  end.
Fixpoint prod_decode_fst (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_fst p
  | p~0~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end
  | p~1~0 => (~0) <$> prod_decode_fst p
  | p~1~1 => Some match prod_decode_fst p with Some q => q~1 | _ => 1 end
  | 1~0 => None
  | 1~1 => Some 1
  | 1 => Some 1
  end.
Fixpoint prod_decode_snd (p : positive) : option positive :=
  match p with
  | p~0~0 => (~0) <$> prod_decode_snd p
  | p~0~1 => (~0) <$> prod_decode_snd p
  | p~1~0 => Some match prod_decode_snd p with Some q => q~1 | _ => 1 end
  | p~1~1 => Some match prod_decode_snd p with Some q => q~1 | _ => 1 end
  | 1~0 => Some 1
  | 1~1 => Some 1
  | 1 => None
  end.

Lemma prod_decode_encode_fst p q : prod_decode_fst (prod_encode p q) = Some p.
Proof.
  assert (∀ p, prod_decode_fst (prod_encode_fst p) = Some p).
  { intros p'. by induction p'; simplify_option_eq. }
  assert (∀ p, prod_decode_fst (prod_encode_snd p) = None).
  { intros p'. by induction p'; simplify_option_eq. }
  revert q. by induction p; intros [?|?|]; simplify_option_eq.
Qed.
Lemma prod_decode_encode_snd p q : prod_decode_snd (prod_encode p q) = Some q.
Proof.
  assert (∀ p, prod_decode_snd (prod_encode_snd p) = Some p).
  { intros p'. by induction p'; simplify_option_eq. }
  assert (∀ p, prod_decode_snd (prod_encode_fst p) = None).
  { intros p'. by induction p'; simplify_option_eq. }
  revert q. by induction p; intros [?|?|]; simplify_option_eq.
Qed.
Program Instance prod_countable `{Countable A} `{Countable B} :
  Countable (A * B)%type := {|
    encode xy := prod_encode (encode (xy.1)) (encode (xy.2));
    decode p :=
     x ← prod_decode_fst p ≫= decode;
     y ← prod_decode_snd p ≫= decode; Some (x, y)
  |}.
Next Obligation.
  intros ?????? [x y]; simpl.
  rewrite prod_decode_encode_fst, prod_decode_encode_snd; simpl.
  by rewrite !decode_encode.
Qed.

(** ** Lists *)
(* Lists are encoded as 1 separated sequences of 0s corresponding to the unary
representation of the elements. *)
Fixpoint list_encode `{Countable A} (acc : positive) (l : list A) : positive :=
  match l with
  | [] => acc
  | x :: l => list_encode (Nat.iter (encode_nat x) (~0) (acc~1)) l
  end.
Fixpoint list_decode `{Countable A} (acc : list A)
    (n : nat) (p : positive) : option (list A) :=
  match p with
  | 1 => Some acc
  | p~0 => list_decode acc (S n) p
  | p~1 => x ← decode_nat n; list_decode (x :: acc) O p
  end.
Lemma x0_iter_x1 n acc : Nat.iter n (~0) acc~1 = acc ++ Nat.iter n (~0) 3.
Proof. by induction n; f_equal/=. Qed.
Lemma list_encode_app' `{Countable A} (l1 l2 : list A) acc :
  list_encode acc (l1 ++ l2) = list_encode acc l1 ++ list_encode 1 l2.
Proof.
  revert acc; induction l1; simpl; auto.
  induction l2 as [|x l IH]; intros acc; simpl; [by rewrite ?(left_id_L _ _)|].
  by rewrite !(IH (Nat.iter _ _ _)), (assoc_L _), x0_iter_x1.
Qed.
Program Instance list_countable `{Countable A} : Countable (list A) :=
  {| encode := list_encode 1; decode := list_decode [] 0 |}.
Next Obligation.
  intros A ??; simpl.
  assert (∀ m acc n p, list_decode acc n (Nat.iter m (~0) p)
    = list_decode acc (n + m) p) as decode_iter.
  { induction m as [|m IH]; intros acc n p; simpl; [by rewrite Nat.add_0_r|].
    by rewrite IH, Nat.add_succ_r. }
  cut (∀ l acc, list_decode acc 0 (list_encode 1 l) = Some (l ++ acc))%list.
  { by intros help l; rewrite help, (right_id_L _ _). }
  induction l as [|x l IH] using @rev_ind; intros acc; [done|].
  rewrite list_encode_app'; simpl; rewrite <-x0_iter_x1, decode_iter; simpl.
  by rewrite decode_encode_nat; simpl; rewrite IH, <-(assoc_L _).
Qed.
Lemma list_encode_app `{Countable A} (l1 l2 : list A) :
  encode (l1 ++ l2)%list = encode l1 ++ encode l2.
Proof. apply list_encode_app'. Qed.
Lemma list_encode_cons `{Countable A} x (l : list A) :
  encode (x :: l) = Nat.iter (encode_nat x) (~0) 3 ++ encode l.
Proof. apply (list_encode_app' [_]). Qed.
Lemma list_encode_suffix `{Countable A} (l k : list A) :
  l `suffix_of` k → ∃ q, encode k = q ++ encode l.
Proof. intros [l' ->]; exists (encode l'); apply list_encode_app. Qed.
Lemma list_encode_suffix_eq `{Countable A} q1 q2 (l1 l2 : list A) :
  length l1 = length l2 → q1 ++ encode l1 = q2 ++ encode l2 → l1 = l2.
Proof.
  revert q1 q2 l2; induction l1 as [|a1 l1 IH];
    intros q1 q2 [|a2 l2] ?; simplify_eq/=; auto.
  rewrite !list_encode_cons, !(assoc _); intros Hl.
  assert (l1 = l2) as <- by eauto; clear IH; f_equal.
  apply (inj encode_nat); apply (inj (++ encode l1)) in Hl; revert Hl; clear.
  generalize (encode_nat a2).
  induction (encode_nat a1); intros [|?] ?; naive_solver.
Qed.

(** ** Numbers *)
Instance pos_countable : Countable positive :=
  {| encode := id; decode := Some; decode_encode x := eq_refl |}.
Program Instance N_countable : Countable N := {|
  encode x := match x with N0 => 1 | Npos p => Pos.succ p end;
  decode p := if decide (p = 1) then Some 0%N else Some (Npos (Pos.pred p))
|}.
Next Obligation.
  intros [|p]; simpl; [done|].
  by rewrite decide_False, Pos.pred_succ by (by destruct p).
Qed.
Program Instance Z_countable : Countable Z := {|
  encode x := match x with Z0 => 1 | Zpos p => p~0 | Zneg p => p~1 end;
  decode p := Some match p with 1 => Z0 | p~0 => Zpos p | p~1 => Zneg p end
|}.
Next Obligation. by intros [|p|p]. Qed.
Program Instance nat_countable : Countable nat :=
  {| encode x := encode (N.of_nat x); decode p := N.to_nat <$> decode p |}.
Next Obligation.
  by intros x; lazy beta; rewrite decode_encode; csimpl; rewrite Nat2N.id.
Qed.

Global Program Instance Qc_countable : Countable Qc :=
  inj_countable
    (λ p : Qc, let 'Qcmake (x # y) _ := p return _ in (x,y))
    (λ q : Z * positive, let '(x,y) := q return _ in Some (Q2Qc (x # y))) _.
Next Obligation.
  intros [[x y] Hcan]. f_equal. apply Qc_is_canon. simpl. by rewrite Hcan.
Qed.

Global Program Instance Qp_countable : Countable Qp :=
  inj_countable
    Qp_car
    (λ p : Qc, guard (0 < p)%Qc as Hp; Some (mk_Qp p Hp)) _.
Next Obligation.
  intros [p Hp]. unfold mguard, option_guard; simpl.
  case_match; [|done]. f_equal. by apply Qp_eq.
Qed.

(** ** Generic trees *)
Close Scope positive.

Inductive gen_tree (T : Type) : Type :=
  | GenLeaf : T → gen_tree T
  | GenNode : nat → list (gen_tree T) → gen_tree T.
Arguments GenLeaf {_} _ : assert.
Arguments GenNode {_} _ _ : assert.

Instance gen_tree_dec `{EqDecision T} : EqDecision (gen_tree T).
Proof.
 refine (
  fix go t1 t2 := let _ : EqDecision _ := @go in
  match t1, t2 with
  | GenLeaf x1, GenLeaf x2 => cast_if (decide (x1 = x2))
  | GenNode n1 ts1, GenNode n2 ts2 =>
     cast_if_and (decide (n1 = n2)) (decide (ts1 = ts2))
  | _, _ => right _
  end); abstract congruence.
Defined.

Fixpoint gen_tree_to_list {T} (t : gen_tree T) : list (nat * nat + T) :=
  match t with
  | GenLeaf x => [inr x]
  | GenNode n ts => (ts ≫= gen_tree_to_list) ++ [inl (length ts, n)]
  end.

Fixpoint gen_tree_of_list {T}
    (k : list (gen_tree T)) (l : list (nat * nat + T)) : option (gen_tree T) :=
  match l with
  | [] => head k
  | inr x :: l => gen_tree_of_list (GenLeaf x :: k) l
  | inl (len,n) :: l =>
     gen_tree_of_list (GenNode n (reverse (take len k)) :: drop len k) l
  end.

Lemma gen_tree_of_to_list {T} k l (t : gen_tree T) :
  gen_tree_of_list k (gen_tree_to_list t ++ l) = gen_tree_of_list (t :: k) l.
Proof.
  revert t k l; fix 1; intros [|n ts] k l; simpl; auto.
  trans (gen_tree_of_list (reverse ts ++ k) ([inl (length ts, n)] ++ l)).
  - rewrite <-(assoc_L _). revert k. generalize ([inl (length ts, n)] ++ l).
    induction ts as [|t ts'' IH]; intros k ts'''; csimpl; auto.
    rewrite reverse_cons, <-!(assoc_L _), gen_tree_of_to_list; simpl; auto.
  - simpl. by rewrite take_app_alt, drop_app_alt, reverse_involutive
      by (by rewrite reverse_length).
Qed.

Program Instance gen_tree_countable `{Countable T} : Countable (gen_tree T) :=
  inj_countable gen_tree_to_list (gen_tree_of_list []) _.
Next Obligation.
  intros T ?? t.
  by rewrite <-(right_id_L [] _ (gen_tree_to_list _)), gen_tree_of_to_list.
Qed.
