Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Isomorphism.
  Universe o h p.
  Context {C : Category@{o h p}}.

  Class Isomorphism (x y : C) :=
    { to : x ~> y
    ; from : y ~> x

    ; iso_to_from : to ∘ from ≡ id[y]
    ; iso_from_to : from ∘ to ≡ id[x]
    }.
    
  Arguments to {x y} _.
  Arguments from {x y} _.
  Arguments iso_to_from {x y} _.
  Arguments iso_from_to {x y} _.

  Infix "≅" := Isomorphism (at level 91) : category_scope.

  Class IsIsomorphism {x y : C} (f : x ~> y) :=
    { two_sided_inverse : y ~> x
    ; is_right_inverse : f ∘ two_sided_inverse ≡ id[y]
    ; is_left_inverse : two_sided_inverse ∘ f ≡ id[x]
    }.

  #[export]
  Program Instance IsIsoToIso {x y : C} (f : x ~> y) (_ : IsIsomorphism f)
    : Isomorphism x y :=
      {| to := f
       ; from := two_sided_inverse
       ; iso_to_from := is_right_inverse
       ; iso_from_to := is_left_inverse
      |}.

  #[export]
  Program Instance iso_id {x : C} : Isomorphism x x :=
    {| to := id[x]
     ; from := id[x]
    |}.

  Program Definition iso_sym {x y : C} (f : x ≅ y) : y ≅ x :=
    {| to := from f
     ; from := to f
     ; iso_to_from := iso_from_to f
     ; iso_from_to := iso_to_from f
    |}.

  Program Definition iso_compose {x y z : C} (f : y ≅ z) (g : x ≅ y) : x ≅ z :=
    {| to := to f ∘ to g
     ; from := from g ∘ from f
    |}.
  Next Obligation.
    rewrite <- comp_assoc, (comp_assoc (to g)).
    do 2 (rewrite iso_to_from; cat).
  Qed.
  Next Obligation.
    rewrite <- comp_assoc, (comp_assoc (from f)).
    do 2 (rewrite iso_from_to; cat).
  Qed.

  #[export]
  Program Instance iso_equivalence : Equivalence Isomorphism :=
    {| Equivalence_Reflexive := @iso_id
     ; Equivalence_Symmetric := @iso_sym
     ; Equivalence_Transitive := λ _ _ _ f g, iso_compose g f
    |}.

  Definition ob_equiv : crelation C := Isomorphism.

  Instance ob_setoid : Setoid C :=
    {| equiv := ob_equiv
     ; setoid_equiv := iso_equivalence
    |}.

  Definition iso_equiv {x y : C} : crelation (x ≅ y) :=
    λ f g, (to f ≡ to g) * (from f ≡ from g).

  #[export]
  Program Instance iso_equiv_equivalence {x y : C} : Equivalence (@iso_equiv x y).
  Next Obligation. now split. Qed.
  Next Obligation. intros ??[]. now split. Qed.
  Next Obligation. intros ???[][]. split; cat. Qed.

  #[export]
  Program Instance iso_setoid {x y : C} : Setoid (x ≅ y) :=
    {| equiv := iso_equiv
     ; setoid_equiv := iso_equiv_equivalence
    |}.

  #[export]
  Program Instance Iso_Proper
    : Proper (Isomorphism ==> Isomorphism ==> iffT) Isomorphism.
  Next Obligation.
    proper.
    - now transitivity x0; [transitivity x; [symmetry|]|].
    - now transitivity y; [|transitivity y0; [|symmetry]].
  Qed.

  (* Example of Use of Iso_Proper *)
  Goal ∀ {F G K} (f : G ≅ K) (g : F ≅ G), F ≅ K.
  Proof. intros. now rewrite g. Qed.
End Isomorphism.

Declare Scope isomorphism_scope.
Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 91) : isomorphism_scope.
Notation "x ≅[ C ] y" := (@Isomorphism C%category x%object y%object)
  (at level 91, only parsing) : isomorphism_scope.

Notation "f ○ g" := (iso_compose f g)
  (at level 40, left associativity) : isomorphism_scope.

Arguments to {_%_category x%_object y%_object} _%_morphism.
Arguments from {_%_category x%_object y%_object} _%_morphism.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

#[export] Hint Unfold iso_equiv : core.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).