Require Export Coq.Lists.List.

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

Section rect.
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
End rect.

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

Inductive NoDup `{Setoid A} : list A → Type :=
  | NoDup_nil : NoDup []
  | NoDup_cons : ∀ x l, ¬ In x l → NoDup l → NoDup (x :: l)
  .

#[export] Hint Constructors Forall Exist In NoDup : core.

Section In.
  Context `{Setoid A}.

  Lemma In_nil_absurd (a : A) : ¬ In a [].
  Proof. inversion 1. Qed.
    
  Lemma In_singleton (a b : A) : In a [b] → a ≡ b.
  Proof. now inversion 1; subst. Qed.

  Lemma In_cons_or (a x : A) (l : list A)
    : In a (x :: l) → x ≡ a ∨ In a l.
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
  Instance In_respects : Proper (equiv ==> equiv ==> iffT) In.
  Proof. now split; apply In_respects_helper. Qed.

  #[export]
  Instance In_property (l : list A) : Property (λ x, In x l).
  Proof. now construct; proper; rewrite <-X. Qed.

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

  Lemma In_app_or_iff (a : A) (l l' : list A)
    : In a (l ++ l') ↔ In a l ∨ In a l'.
  Proof. split; [apply In_app_or|apply In_or_app]. Qed.

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
    : Forall P l ↔ ∀ a, In a l → P a.
  Proof.
    split.
    - induction 1; [now intros ??%In_nil_absurd|].
      intros ? []%In_cons_or; rewrite <- ?e; auto.
    - induction l; intuition.
  Qed.

  Lemma Forall_app `{Property A P} (l1 l2: list A)
    : Forall P (l1 ++ l2) ↔ (Forall P l1 ∧ Forall P l2).
  Proof.
    rewrite !Forall_forall; split
    ; intuition; auto using In_or_app.
    apply In_app_or in X as [X|X]; auto.
  Qed.
  
  Lemma Forall_cons_and `{Property A P} (a : A) (l : list A)
    : Forall P (a :: l) → (P a ∧ Forall P l).
  Proof. now inversion 1; subst. Qed.
End Forall.

Section Exist.
  Lemma Exist_exists `{Property A P} (l : list A)
    : Exist P l ↔ ∃ a, In a l ∧ P a.
  Proof.
    split.
    - induction 1; [exists x; intuition|].
      destruct IHX as [a [HIn HP]]; exists a; intuition.
    - intros [a [HIn HP]]. revert HP; induction HIn; auto.
      constructor. now eapply H0; eauto.
  Qed.

  Lemma Exist_app `{Property A P} (l1 l2 : list A)
    : Exist P (l1 ++ l2) ↔ (Exist P l1 ∨ Exist P l2).
  Proof.
    rewrite !Exist_exists; split.
    - intros [a [[IN|IN]%In_app_or Pa]]; eauto.
    - intros [[a [IN Pa]]|[a [IN Pa]]]; eauto using In_or_app.
  Qed.

  Lemma Exist_cons_or `{Property A P} (a : A) (l : list A)
    : Exist P (a :: l) → P a ∨ Exist P l.
  Proof. inversion 1; subst; auto. Qed.
End Exist.

Section NoDup.
  Context `{Setoid A}.

  Lemma NoDup_inv (l : list A)
    : NoDup l
    → match l with
      | [] => poly_unit
      | x :: l' => ¬ In x l' ∧ NoDup l'
      end.
  Proof. destruct l; inversion 1; auto. Qed.

  Lemma NoDup_app_remove_r (l1 l2 : list A)
    : NoDup (l1 ++ l2) → NoDup l1.
  Proof.
    induction l1; auto.
    inversion 1; subst.
    econs; auto. rewrite In_app_or_iff in X0.
    intro; apply X0. now left.
  Qed.

  Lemma NoDup_app_remove_l (l1 l2 : list A)
    : NoDup (l1 ++ l2) → NoDup l2.
  Proof. induction l1; auto. inversion 1; auto. Qed.

  Lemma NoDup_rcons (a : A) (l : list A)
    : NoDup (l ++ [a]) → ¬ In a l.
  Proof.
    induction l; s.
    - ii. inversion X0.
    - inversion 1; subst. ii.
      apply In_cons_or in X2.
      destruct X2; intuition.
      rewrite <-e in X0. apply X0, In_or_app.
      right. now econs.
  Qed.

  Lemma NoDup_app (l1 l2 : list A)
    : (∀ a, In a l1 → ¬ In a l2)
    → NoDup l1 → NoDup l2 → NoDup (l1 ++ l2).
  Proof.
    revert l2. induction l1 using rev_rect; auto.
    i. rewrite <- app_assoc.
    apply IHl1; [| now apply NoDup_app_remove_r in X0
                 | econs; auto; now apply X, In_or_app; right; econs
                 ].
    ii. apply In_cons_or in X3.
    destruct X3; [|apply (X a); [apply In_or_app|]]; auto.
    apply NoDup_rcons in X0; apply X0. now rewrite e.
  Qed.
End NoDup.

Section Last.
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

  Lemma last_Forall `{Property A P} (x y : A) l
    : last l x ≡ y → Forall P l → P x → P y.
  Proof.
    revert x. destruct l using rev_rect; ss.
    - now rewrite <-X.
    - rewrite last_rcons in X.
      apply Forall_app in X0 as [X0 X2].
      rewrite <-X. now inversion X2.
  Qed.
End Last.

Section Decidable.
  Context `{EqDec : @Decidable A SET}.

  Lemma In_Dec x l : In x l ∨ ¬ In x l.
  Proof.
    induction l; [right; inversion 1|].
    destruct IHl as [? | IHl]; eauto.
    destruct (dec_equiv a x) as [-> | ne]; [now left; econs|].
    right; inversion 1; eauto.
  Qed.
End Decidable.