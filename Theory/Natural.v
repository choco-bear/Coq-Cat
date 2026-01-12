Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Reserved Infix "⟹" (at level 90, right associativity).
Reserved Infix "⋅" (at level 40, left associativity).

Generalizable All Variables.

(** A natural transformation between two functors is a family of morphisms that is
  * "natural" in a specific sense. *)
Section NaturalTransform.
  Context {C : Category}.
  Context {D : Category}.
  Context {F G : C ⟶ D}.

  Class NaturalTransform : Type :=
    { component : ∀ (x : C), F x ~> G x
    ; naturality `(f : x ~{C}~> y) :
        component y ∘ fmap[F] f ≡ fmap[G] f ∘ component x
    }.
  
  #[export]
  Program Instance NaturalTransform_Setoid
    : Setoid (NaturalTransform) :=
      {| equiv := λ η μ, ∀ x : C, @component η x ≡ @component μ x |}.
  Next Obligation. equivalence. now rewrites. Defined.
End NaturalTransform.

Arguments component {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

#[export] Hint Rewrite @naturality : normalize.

Declare Scope natural_scope.
Declare Scope natural_type_scope.
Bind Scope natural_scope with NaturalTransform.
Delimit Scope natural_scope with natural.
Delimit Scope natural_type_scope with natural_type.

Open Scope natural_scope.
Open Scope natural_type_scope.

Notation "F ⟹ G" := (@NaturalTransform _ _ F G)
  (at level 90, right associativity) : natural_type_scope.
Coercion component : NaturalTransform >-> Funclass.

Notation "'component[' F '⟹' G ']'" :=
  (@component _ _ F G) (at level 0, only parsing) : natural_scope.
Notation "'naturality[' F '⟹' G ']'" :=
  (@naturality _ _ F G) (at level 0, only parsing) : natural_scope.

(** Tactic for creating natural transformations *)
Ltac natural_transform := unshelve (refine {| component := _ |}; simpl; intros).

Program Definition NaturalTransform_id `{F : C ⟶ D} : F ⟹ F :=
  {| component := λ x, id[F x] |}.

(** Vertical Composition of Natural Transformations *)
Section VerticalComposition.
  Context {C : Category} {D : Category}.
  Context {F G H : C ⟶ D}.

  Program Definition NaturalTransform_vertical_compose
    (η : G ⟹ H) (μ : F ⟹ G) : F ⟹ H := {| component := λ x, η x ∘ μ x |}.
  Next Obligation.
    rewrite <- comp_assoc, naturality.
    by rewrite comp_assoc, naturality.
  Qed.

  #[export]
  Program Instance NaturalTransform_vertical_compose_respects
    : Proper (equiv ==> equiv ==> equiv) NaturalTransform_vertical_compose.
End VerticalComposition.

Notation "η ⋅ μ" := (NaturalTransform_vertical_compose η μ)
  (at level 40, left associativity) : natural_scope.

(** Horizontal Composition of Natural Transformations *)
Section HorizontalComposition.
  Context {A : Category} {B : Category} {C : Category}.
  Context {S T : C ⟶ B} {S' T' : B ⟶ A}.

  Program Definition NaturalTransform_horizontal_compose
    (τ' : S' ⟹ T') (τ : S ⟹ T) : S' ◯ S ⟹ T' ◯ T :=
      {| component := λ c, fmap[T'] (τ c) ∘ τ' (S c) |}.
  Next Obligation.
    rewrite <-comp_assoc, naturality, !comp_assoc. comp_right.
    assert (τ y ∘ fmap[S] f ≡ fmap[T] f ∘ τ x) by now normalize.
    now rewrite <-!fmap_comp; rewrites.
  Qed.

  #[export]
  Program Instance NaturalTransform_horizontal_compose_respects
    : Proper (equiv ==> equiv ==> equiv) NaturalTransform_horizontal_compose.
  Next Obligation. now proper; rewrites. Qed.
End HorizontalComposition.

Notation "τ' ▪ τ" := (NaturalTransform_horizontal_compose τ' τ)
  (at level 40, left associativity) : natural_scope.