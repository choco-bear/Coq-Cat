Require Import Coq.Lists.List.

Require Export Category.Lib.Tactics.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import ListNotations.

Section ListSetoid.
  Fixpoint list_equiv `{Setoid A} (xs ys : list A) : Type :=
    match xs, ys with
    | nil, nil => poly_unit
    | x :: xs, y :: ys => x ≡ y ∧ list_equiv xs ys
    | _, _ => poly_void
    end.

  #[global]
  Program Instance list_equivalence `{Setoid A} : Equivalence list_equiv.
  Next Obligation.
    induction x; simpl; simplify; auto.
    reflexivity.
  Qed.
  Next Obligation.
    induction x, y; simpl; intros; simplify; auto.
    now symmetry.
  Qed.
  Next Obligation.
    induction x, y, z; simpl; intros;
    simplify; auto; try contradiction.
    - now transitivity a0.
    - firstorder.
  Qed.

  #[global]
  Program Instance list_setoid `{Setoid A} : Setoid (list A) :=
    { equiv := list_equiv }.

  #[global]
  Program Instance cons_respects {A} `{Setoid A}
    : Proper (equiv ==> equiv ==> equiv) (@cons A).

  #[global]
  Program Instance app_respects {A} `{Setoid A}
    : Proper (equiv ==> equiv ==> equiv) (@app A).
  Next Obligation.
    proper.
    generalize dependent y.
    induction x, y; simpl; intros; auto.
    - contradiction.
    - contradiction.
    - simplify; auto.
  Qed.
End ListSetoid.

Inductive Forall [A : Type] (P : A → Type) : list A → Type :=
  | Forall_nil : Forall P []
  | Forall_cons : ∀ x l, P x → Forall P l → Forall P (x :: l)
  .

Inductive Exist [A : Type] (P : A → Type) : list A → Type :=
  | Exist_cons : ∀ x l, P x → Exist P (x :: l)
  | Exist_skip : ∀ x l, Exist P l → Exist P (x :: l)
  .

Inductive In `{Setoid A} (a : A) : list A → Type :=
  | In_cons : ∀ x l, x ≡ a → In a (x :: l)
  | In_skip : ∀ x l, In a l → In a (x :: l)
  .

#[export] Hint Constructors Forall Exist In : core.

Section In.
  Context `{Setoid A}.

  Lemma In_nil_absurd (a : A) : ¬ In a [].
  Proof. inversion 1. Qed.
    
  Lemma In_singleton (a b : A) : In a [b] → a ≡ b.
  Proof. now inversion 1; subst. Qed.

  Lemma In_cons_or (a x : A) (l : list A)
    : In a (x :: l) → a ≡ x ∨ In a l.
  Proof. now inversion 1; subst; [left|right]. Qed.

  Lemma In_or_cons (a x : A) (l : list A)
    : a ≡ x ∨ In a l → In a (x :: l).
  Proof. intros []; auto. now apply In_cons. Qed.

  Definition In_respects_helper
    : Proper (equiv ==> equiv ==> Basics.arrow) In.
  Proof.
    proper. revert y0 X0.
    induction X1; destruct y0; try done; intros []; auto.
    apply In_cons. now rewrite <-e0, e.
  Qed.
    
  #[export]
  Program Instance In_respects
    : Proper (equiv ==> equiv ==> iffT) In.
  Next Obligation. now split; apply In_respects_helper. Qed.

  Lemma In_or_app (a : A) (l l' : list A)
    : In a l ∨ In a l' → In a (l ++ l').
  Proof.
    intros [HIn|HIn]; [induction HIn|induction l]; simpl; auto.
  Qed.

  Lemma In_app_or (a : A) (l l' : list A)
    : In a (l ++ l') → In a l ∨ In a l'.
  Proof.
    revert l'. induction l; auto.
    simpl; inversion 1; auto.
    apply IHl in X0 as []; auto.
  Qed.

  Context `{Setoid B}.
  Lemma In_map (a : A) (l : list A) (f : A → B)
    : Proper (equiv ==> equiv) f
    → In a l
    → In (f a) (map f l).
  Proof.
    intro. induction 1; simpl.
    - now left; rewrite e.
    - now right.
  Qed.
End In.

Section Forall.
  Lemma Forall_forall `{Property A P} (l : list A)
    : Forall P l ↔ ∀ a : A, In a l → P a.
  Proof.
    split.
    - induction 1; [now intros ??%In_nil_absurd|].
      intros ? []%In_cons_or; rewrite ?e; auto.
    - induction l; intuition.
  Qed.
End Forall.

Definition rev_list_rect (A : Type) (P : list A → Type) (H : P [])
  (H0 : ∀ (a : A) (l : list A), P (rev l) → P (rev (a :: l))) (l : list A)
  : P (rev l) :=
    list_rect (λ l0 : list A, P (rev l0)) H
      (λ (a : A) (l0 : list A) (IHl : P (rev l0)), H0 a l0 IHl) l.

Definition rev_rect (A : Type) (P : list A → Type)
  (H : P []) (H0 : ∀ (x : A) (l : list A), P l → P (l ++ [x])) (l : list A)
  : P l :=
    (λ E : rev (rev l) = l,
      eq_rect (rev (rev l)) (λ l0 : list A, P l0)
        (rev_list_rect A P H
          (λ (a : A) (l0 : list A) (H1 : P (rev l0)), H0 a (rev l0) H1)
          (rev l)) l E) (rev_involutive l).

Definition list_rect2 (A : Type) (P : list A → list A → Type)
  (H : P [] []) (H0 : ∀ (a : A) (l1 : list A), P l1 [] → P (a :: l1) [])
  (H1 : ∀ (b : A) (l2 : list A), P [] l2 → P [] (b :: l2))
  (H2 : ∀ (a b : A) (l1 l2 : list A), P l1 l2 → P (a :: l1) (b :: l2))
  (l1 l2 : list A)
  : P l1 l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1; simpl in *; intros;
  induction l2; auto.
Defined.

Lemma last_rcons A (x y : A) l : last (l ++ [x]) y = x.
Proof.
  induction l; simpl.
    reflexivity.
  rewrite IHl; clear IHl.
  destruct l; auto.
Qed.

Lemma last_app_cons A (x : A) xs y ys : last (xs ++ y :: ys) x = last (y :: ys) x.
Proof.
  generalize dependent y.
  generalize dependent xs.
  induction ys using rev_ind; simpl; intros.
    apply last_rcons.
  rewrite last_rcons.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite last_rcons.
  destruct ys; auto.
Qed.

Lemma last_cons A (x : A) y ys : last (y :: ys) x = last ys y.
Proof.
  generalize dependent x.
  induction ys using rev_ind; simpl; intros.
    reflexivity.
  rewrite !last_rcons.
  destruct ys; auto.
Qed.

Lemma match_last {A} {a : A} {xs x}
  : match xs with
    | [] => a
    | _ :: _ => last xs x
    end = last xs a.
Proof.
  induction xs; auto.
  rewrite !last_cons; reflexivity.
Qed.

Lemma map_inj {A B : Type} (f : A → B) (f_inj : ∀ x y, f x = f y → x = y) xs ys
  : List.map f xs = List.map f ys → xs = ys.
Proof.
  generalize dependent ys.
  induction xs, ys; simpl; intros; auto; try inv H.
  apply f_inj in H1; subst.
  f_equal.
  now apply IHxs.
Qed.

(** TODO : Define [Forall] without using [Prop] universe, and comment out the below. *)
(* Lemma Forall_app [A : Type] (P : A → Type) (l1 l2: list A)
  : Forall P (l1 ++ l2) ↔ (Forall P l1 ∧ Forall P l2).
Proof.
  intros.
  rewrite !Forall_forall.
  split; intros.
    split; intros;
    apply H; apply in_or_app.
      left; trivial.
    right; trivial.
  apply in_app_or in H0.
  destruct H, H0; eauto.
Qed.

Lemma last_Forall A (x y : A) l P : last l x = y → Forall P l → P x → P y.
Proof.
  generalize dependent x.
  destruct l using rev_ind; simpl; intros.
    now subst.
  rewrite last_rcons in H; subst.
  apply Forall_app in H0.
  destruct H0.
  now inversion H0.
Qed. *)