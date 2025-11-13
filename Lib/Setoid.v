Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Vectors.Fin.
Require Export Category.Lib.Base.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Setoid (A : Type) : Type :=
  { equiv : crelation A
  ; setoid_equiv : Equivalence equiv
  }.
#[export] Existing Instance setoid_equiv.

Coercion setoid_equiv : Setoid >-> Equivalence.

Notation "f ≡ g" := (equiv f g) (at level 79) : category_theory_scope.
Notation "f '≡[' A ']' g" := (@equiv A _ f g)
  (at level 79, only parsing) : category_theory_scope.

Definition eq_equivalence {A : Type} : @Equivalence A (@eq A) :=
  @Build_Equivalence A (@eq A : crelation A)
    (@eq_Reflexive A) (@eq_Symmetric A) (@eq_Transitive A).

Inductive poly_unit : Type := ttt.

Definition unit_setoid : Setoid poly_unit :=
  {| equiv := @eq poly_unit
   ; setoid_equiv := @eq_equivalence poly_unit
  |}.

Definition eq_Setoid (A : Type) : Setoid A :=
  Build_Setoid A (λ f g, eq f g) eq_equivalence.

#[export]
Program Instance funext_Setoid
  {T : Type} (t : T → Type) (a b : T) {SETOID : Setoid (t b)}
  : Setoid (t a → t b) | 9 :=
    {| equiv        := λ f g, ∀ x, f x ≡ g x
     ; setoid_equiv := @Build_Equivalence (t a → t b) _
                       (λ f x, @Equivalence_Reflexive (t b) _ _ (f x))
                       (λ f g Heq x, @Equivalence_Symmetric (t b) _ _ (f x) (g x) (Heq x))
                       (λ f g h Hfg Hgh x, @Equivalence_Transitive (t b) _ _ (f x) (g x) (h x) (Hfg x) (Hgh x))
    |}.

#[export]
Program Instance Fin_Setoid {n} : Setoid (Fin.t n) := eq_Setoid (Fin.t n).

Class Unique `{S : Setoid A} (P : A → Type) :=
  { unique_obj : A
  ; unique_property : P unique_obj
  ; uniqueness      : ∀ v : A, P v → unique_obj ≡ v
  }.

Arguments unique_obj {_ _ _} _.
Arguments unique_property {_ _ _} _.
Arguments uniqueness {_ _ _} _.

Notation "∃! x .. y , P" := (Unique (fun x => .. (Unique (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : category_theory_scope.

Local Set Warnings "-not-a-class".

Class injective
  {A : Type} `{Setoid A}
  {B : Type} `{Setoid B} (f : A -> B) :=
  { inj {x y} : f x ≡ f y -> x ≡ y }.

Class surjective
  {A : Type} {B : Type} `{Setoid B} (f : A -> B) :=
  { surj {y} : { x & f x ≡ y} }.

Local Set Warnings "not-a-class".