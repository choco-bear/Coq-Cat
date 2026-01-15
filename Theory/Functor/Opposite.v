Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

Generalizable Variables All.

Section Defs.
  Context {B : Category} {C : Category}.

  Program Definition OppositeTranslate (T : B ⟶ C) : B^op ⟶ C^op :=
    {|  fobj := λ x : obj[B^op], T x : obj[C^op]
      ; fmap := λ x y f, fmap[T] f
    |}.
End Defs.

Notation "'↥'" := OppositeTranslate : functor_scope.
Notation "'↥[' B ',' C ']'" :=
  (@OppositeTranslate B%category C%category) (only parsing) : functor_scope.