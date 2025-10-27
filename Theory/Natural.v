Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Reserved Infix "⟹" (at level 90, right associativity).
Reserved Infix "⋅" (at level 40, left associativity).

Generalizable All Variables.

(** A natural transformation between two functors is a family of morphisms that is
  * "natural" in a specific sense. *)
Section NaturalTransform.
  Universes o1 h1 p1 o2 h2 p2.
  Context {C : Category@{o1 h1 p2}}.
  Context {D : Category@{o2 h2 p2}}.
  Context {F G : C ⟶ D}.

  Class NaturalTransform : Type :=
    { component : ∀ (x : C), F x ~> G x
    ; naturality `(f : x ~{C}~> y) :
        component y ∘ fmap[F] f ≡ fmap[G] f ∘ component x
    }.
  
  #[export]
  Program Instance NaturalTransform_Setoid
    : Setoid (NaturalTransform) :=
      {| equiv := λ η μ,
          ∀ x : C, @component η x ≡ @component μ x
      |}.
  Next Obligation. equivalence. now rewrites. Defined.
End NaturalTransform.

Arguments component {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

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

(** Composing natural transformations *)
Section Composition.
  Context {C : Category}.
  Context {D : Category}.
  Context {F G H : C ⟶ D}.
  Program Definition NaturalTransform_compose
    (η : G ⟹ H) (μ : F ⟹ G) : F ⟹ H :=
    {| component := λ x, η x ∘ μ x
      ; naturality := λ x y f, _
    |}.
  Next Obligation.
    rewrite <- comp_assoc, naturality.
    by rewrite comp_assoc, naturality.
  Qed.

  Program Instance NaturalTransform_compose_respects
    : Proper (equiv ==> equiv ==> equiv) NaturalTransform_compose.
End Composition.

Notation "η ⋅ μ" := (NaturalTransform_compose η μ)
  (at level 40, left associativity) : natural_scope.