Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Vectors.Fin.
Require Export Category.Lib.Base.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Printing Universes.
Unset Transparent Obligations.

Class Setoid@{t u} (A : Type@{t}) : Type@{max(t, u+1)} :=
  { equiv : crelation@{t u} A
  ; setoid_equiv : Equivalence@{t u} equiv
  }.
#[export] Existing Instance setoid_equiv.

Coercion setoid_equiv : Setoid >-> Equivalence.

Notation "f ≡ g" := (equiv f g) (at level 79) : category_theory_scope.
Notation "f '≡[' A ']' g" := (@equiv A _ f g)
  (at level 79, only parsing) : category_theory_scope.

Definition eq_Reflexive@{t u} {A : Type@{t}} : Reflexive@{t u} (@eq A) :=
  λ x, eq_refl.

Definition eq_Symmetric@{t u} {A : Type@{t}} : Symmetric@{t u} (@eq A) :=
  λ (x y : A) (e : x = y), match e in (_ = a) return (a = x) with
                           | eq_refl => eq_refl
                           end.

Definition eq_Transitive@{t u} {A : Type@{t}} : Transitive@{t u} (@eq A) :=
  λ (x y z : A) (Hxy : x = y) (Hyz : y = z), match Hyz in (_ = a) return (x = a) with
                                             | eq_refl => Hxy
                                             end.

Definition eq_equivalence@{t u} {A : Type@{t}} : @Equivalence@{t u} A (@eq A) :=
  @Build_Equivalence@{t u} A
    (@eq A : crelation@{t u} A) (@eq_Reflexive@{t u} A) (@eq_Symmetric@{t u} A) (@eq_Transitive@{t u} A).

Inductive poly_unit@{u} : Type@{u} := ttt.

Definition unit_setoid@{t u} : Setoid@{t u} poly_unit@{t} :=
  {| equiv := @eq poly_unit@{t}
   ; setoid_equiv := @eq_equivalence@{t u} poly_unit@{t}
  |}.

Definition eq_Setoid@{t u} (A : Type@{t}) : Setoid@{t u} A :=
  Build_Setoid@{t u} A (λ f g, eq f g) eq_equivalence@{t u}.

#[export]
Program Instance funext_Setoid@{t1 t2 u}
  {T : Type@{t1}} (t : T → Type@{t2}) (a b : T) {SETOID : Setoid@{t2 u} (t b)}
  : Setoid@{t2 u} (t a → t b) | 9 :=
    {| equiv        := λ f g, ∀ x, f x ≡ g x
     ; setoid_equiv := @Build_Equivalence@{t2 u} (t a → t b) _
                       (λ f x, @Equivalence_Reflexive (t b) _ _ (f x))
                       (λ f g Heq x, @Equivalence_Symmetric (t b) _ _ (f x) (g x) (Heq x))
                       (λ f g h Hfg Hgh x, @Equivalence_Transitive (t b) _ _ (f x) (g x) (h x) (Hfg x) (Hgh x))
    |}.

#[export]
Program Instance Fin_Setoid@{u} {n} : Setoid@{Set u} (Fin.t n) :=
  eq_Setoid@{Set u} (Fin.t n).

Class Unique@{t u p} `{S : Setoid@{t u} A} (P : A → Type@{p}) :=
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

Class injective@{t1 u1 t2 u2}
  {A : Type@{t1}} `{Setoid@{t1 u1} A}
  {B : Type@{t2}} `{Setoid@{t2 u2} B} (f : A -> B) :=
  { inj {x y} : f x ≡ f y -> x ≡ y }.

Class surjective@{t1 t2 u}
  {A : Type@{t1}} {B : Type@{t2}} `{Setoid@{t2 u} B} (f : A -> B) :=
  { surj {y} : { x & f x ≡ y} }.

Local Set Warnings "not-a-class".