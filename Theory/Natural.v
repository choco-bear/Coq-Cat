Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Reserved Infix "⟹" (at level 50, left associativity).

Generalizable All Variables.

Section NaturalTransformation.
  Class NaturalTransformation {C D : Category} (F G  : C ⟶ D) : Type :=
    { component : ∀ (x : C), F x ~> G x
    ; naturality `(f : x ~{C}~> y) :
        component y ∘ fmap[F] f ≡ fmap[G] f ∘ component x
    }.
End NaturalTransformation.
