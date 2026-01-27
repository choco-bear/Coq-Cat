Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

Section Defs.
  Context {B : Category} {C : Category} (T : B ⟶ C).

  Program Definition OppositeTranslate : B^op ⟶ C^op :=
    {|  fobj := λ x : obj[B^op], T x : obj[C^op]
      ; fmap := λ x y f, fmap[T] f
    |}.

  Definition fobj_OppositeTranslate x : OppositeTranslate x = T x := eq_refl.

  Definition fmap_OppositeTranslate `(f : x ~{B^op}~> y) : fmap[OppositeTranslate] f = fmap[T] f := eq_refl.
End Defs.
#[export] Arguments OppositeTranslate {B C}%_category (T)%_functor : simpl never.
#[export] Hint Rewrite @fobj_OppositeTranslate @fmap_OppositeTranslate : categories normalize.

Notation "'↥'" := OppositeTranslate : functor_scope.
Notation "'↥[' B ',' C ']'" :=
  (@OppositeTranslate B%category C%category) (only parsing) : functor_scope.