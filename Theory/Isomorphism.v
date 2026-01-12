Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

Section Isomorphism.
  Context {C : Category}.

  (** An isomorphism between two objects [x] and [y] in a category [C] is a
    * pair of morphisms [to : x ~> y] and [from : y ~> x] such that
    * [to ∘ from ≡ id[y]] and [from ∘ to ≡ id[x]].
    * Informally, isomorphisms are "invertible" morphisms.
    *)
  Class Isomorphism (x y : C) :=
    { to : x ~> y
    ; from : y ~> x

    ; iso_to_from : to ∘ from ≡ id[y]
    ; iso_from_to : from ∘ to ≡ id[x]
    }.
  #[local] Hint Resolve @to @from : category_laws.
    
  Arguments to {x y} _.
  Arguments from {x y} _.
  Arguments iso_to_from {x y} _.
  Arguments iso_from_to {x y} _.

  Local Infix "≅" := Isomorphism (at level 74).

  (** A morphism [f] between two objects [x] and [y] in a category [C] is said to be
    * an isomorphism if there exists a morphism [g : y ~> x] such that
    * [f ∘ g ≡ id[y]] and [g ∘ f ≡ id[x]].
    *)
  Class IsIsomorphism {x y : C} (f : x ~> y) :=
    { two_sided_inverse : y ~> x
    ; is_right_inverse : f ∘ two_sided_inverse ≡ id[y]
    ; is_left_inverse : two_sided_inverse ∘ f ≡ id[x]
    }.

  #[export]
  Instance IsIsoToIso {x y : C} (f : x ~> y) (_ : IsIsomorphism f)
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

  Definition iso_sym {x y : C} (f : x ≅ y) : y ≅ x :=
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
  Instance iso_equivalence : Equivalence Isomorphism :=
    {| Equivalence_Reflexive := @iso_id
     ; Equivalence_Symmetric := @iso_sym
     ; Equivalence_Transitive := λ _ _ _ f g, iso_compose g f
    |}.

  (** Equivalence relation on objects *)
  Definition ob_equiv : crelation C := Isomorphism.

  Definition ob_setoid : Setoid C :=
    {| equiv := ob_equiv
     ; setoid_equiv := iso_equivalence
    |}.

  Definition iso_equiv {x y : C} : crelation (x ≅ y) :=
    λ f g, (to f ≡ to g).

  #[export]
  Program Instance iso_equiv_equivalence {x y : C} : Equivalence (@iso_equiv x y).
  Next Obligation. now unfold iso_equiv. Qed.
  Next Obligation. now unfold iso_equiv. Qed.
  Next Obligation. now unfold iso_equiv; intros; transitivity (to y0). Qed.

  #[export]
  Instance iso_setoid {x y : C} : Setoid (x ≅ y) :=
    {| equiv := iso_equiv
     ; setoid_equiv := iso_equiv_equivalence
    |}.

  #[export]
  Instance Iso_Proper
    : Proper (Isomorphism ==> Isomorphism ==> iffT) Isomorphism.
  Proof.
    proper.
    - now transitivity x0; [transitivity x; [symmetry|]|].
    - now transitivity y; [|transitivity y0; [|symmetry]].
  Qed.

  #[export]
  Instance proper_from {x y : C} : Proper (equiv ==> equiv) (@from x y).
  Proof.
    proper. rename x0 into f. rename y0 into g. unfold iso_equiv in X.
    rewrite <-id_right, <-(id_right (from g)), <-(iso_to_from f).
    now rewrite !comp_assoc, iso_from_to, X, iso_from_to.
  Qed.

  #[export]
  Instance proper_to {x y : C} : Proper (equiv ==> equiv) (@to x y).
  Proof. proper. Qed.

  (* Example of Use of Iso_Proper *)
  Goal ∀ {F G K} (f : G ≅ K) (g : F ≅ G), F ≅ K.
  Proof. intros. now rewrite g. Qed.

  Lemma iso_simpl_1 {x y z : C} (f : y ~> z) (g : x ≅ y)
    : f ∘ to g ∘ from g ≡ f.
  Proof. by rewrite <-comp_assoc, iso_to_from. Qed.

  Lemma iso_simpl_2 {x y z : C} (f : y ~> z) (g : y ≅ x)
    : f ∘ from g ∘ to g ≡ f.
  Proof. by rewrite <-comp_assoc, iso_from_to. Qed.
End Isomorphism.
#[export] Hint Resolve @to @from : category_laws.
#[export] Hint Rewrite @iso_to_from @iso_from_to @iso_simpl_1 @iso_simpl_2
                       : categories normalize.

Declare Scope isomorphism_scope.
Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 74) : isomorphism_scope.
Notation "x ≅[ C ] y" := (@Isomorphism C%category x%object y%object)
  (at level 74, only parsing) : isomorphism_scope.

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
  unshelve (refine {| to := _; from := _ |}; simpl; repeat intro).

Definition from_compose_natural `(f : y ≅[C] z) `(g : x ≅[C] y)
  : (f ○ g)⁻¹ = g⁻¹ ∘ f⁻¹ := eq_refl.

(** Lemmas related to the [Category.Theory.Morphisms] module. *)
Section Morphisms.
  Context {C : Category}.

  Program Instance iso_epi {x y : C} (f : x ≅ y) : Epic f.
  Next Obligation.
    rewrite <- id_right, <- (iso_to_from f), comp_assoc.
    rewrite X, <- comp_assoc, iso_to_from. cat.
  Qed.

  Program Instance iso_monic {x y : C} (f : x ≅ y) : Monic f.
  Next Obligation.
    rewrite <- id_left, <- (iso_from_to f), <- comp_assoc.
    rewrite X, comp_assoc, iso_from_to. cat.
  Qed.
End Morphisms.