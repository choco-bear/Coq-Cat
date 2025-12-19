From Coq Require Import Classes.RelationClasses
                        Setoids.Setoid
                        Vectors.Fin
                        ZArith.
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

Definition unit_setoid : Setoid poly_unit :=
  {| equiv := @eq poly_unit
   ; setoid_equiv := @eq_equivalence poly_unit
  |}.

Definition void_setoid : Setoid poly_void :=
  {| equiv := @eq poly_void
   ; setoid_equiv := @eq_equivalence poly_void
  |}.

Definition poly_exfalso [T : Type] (CONTRA : poly_void) : T :=
  match CONTRA return T with end.

Program Definition iffT_equivalence : Equivalence iffT :=
  {| Equivalence_Reflexive  := iffT_Reflexive
   ; Equivalence_Symmetric  := iffT_Symmetric
   ; Equivalence_Transitive := iffT_Transitive
  |}.

Program Definition type_setoid : Setoid Type :=
  {| equiv := iffT
   ; setoid_equiv := iffT_equivalence
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

Class Singleton `(S : Setoid A) :=
  { single_element : A
  ; is_singleton   : ∀ a : A, single_element ≡ a
  }.

Program Instance unit_singleton : Singleton unit_setoid :=
  {| single_element := ttt |}.
Next Obligation. now destruct a. Qed.

Definition singleton_unique `{S : Setoid A} {SINGLE : Singleton S} (P : A → Type)
  : P single_element → Unique P :=
    λ HP, {|  unique_obj := single_element
            ; unique_property := HP
            ; uniqueness := λ v _, is_singleton v
          |}.

Program Definition subset `(S : Setoid A) (Φ : A → Type)
  : Setoid (∃ a : A, Φ a) :=
    {| equiv := λ x y, `1 x ≡ `1 y |}.
Next Obligation. now constructor; intuition; repeat intro; transitivity (`1 y). Qed.
Notation "'{' S '&' Φ '}'" := (subset S Φ) : category_theory_scope.

Class Injective
  {A : Type} `{Setoid A}
  {B : Type} `{Setoid B} (f : A -> B) :=
  { inj {x y} : f x ≡ f y -> x ≡ y }.

Class Surjective
  {A : Type} {B : Type} `{Setoid B} (f : A -> B) :=
  { surj {y} : { x & f x ≡ y} }.

Class Operation A `{Setoid A} :=
  { op        : A → A → A
  ; op_proper : Proper (equiv ==> equiv ==> equiv) op
  }.
#[export] Existing Instance op_proper.

Class Commutative `(Operation A) :=
  { commutative {x y} : op x y ≡ op y x }.

Class Property `{Setoid A} (P : A → Type) :=
  { property_proper : Proper (equiv ==> iffT) P }.
#[export] Existing Instance property_proper.

#[export]
Instance proper_nat_iter `{Setoid A} n
  : Proper ((equiv ==> equiv) ==> equiv ==> equiv) (@Nat.iter n A).
Proof. now induction n; repeat intro; simpl; try apply X, IHn. Qed.

#[export]
Instance proper_pos_iter `{Setoid A}
  : Proper ((equiv ==> equiv) ==> equiv ==> eq ==> equiv) (@Pos.iter A).
Proof.
  repeat intro; subst. revert x0 y0 X0.
  induction y1 as [p|p|]; simpl; intros
  ; now try apply X; try do 2 apply IHp.
Qed.

#[export]
Instance proper_Z_iter `{Setoid A} n
  : Proper ((equiv ==> equiv) ==> equiv ==> equiv) (@Z.iter n A).
Proof.
  destruct n; repeat intro; intuition.
  now apply proper_pos_iter.
Qed.