Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** The opposite category [C^op] of [C] is the category whose objects are the same
  * as those of [C], but whose morphisms are reversed.
  *)
Program Definition Opposite (C : Category) : Category :=
  {| obj := @obj C
   ; hom := λ x y, @hom C y x
   ; homset := λ x y, @homset C y x
   ; id := λ x, @id C x
   ; compose := λ x y z f g, g ∘ f
  |}.

Notation "C '^op'" := (Opposite C) (at level 0, format "C '^op'") : category_scope.