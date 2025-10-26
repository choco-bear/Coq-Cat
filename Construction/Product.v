Require Import Category.Lib.
Require Import Category.Theory.Category.

(** Being given two categories [C] and [D], we can construct their product category
  * [C × D], which has objects that are pairs of objects in [C] and objects in [D],
  * and morphisms that are pairs of morphisms.
  *)
Program Definition Product (C D : Category) : Category :=
  {| obj := obj[C] * obj[D]
   ; hom := λ x y, (hom (fst x) (fst y)) * (hom (snd x) (snd y))
   ; homset := λ x y, prod_setoid
   ; id := λ x, (id[fst x], id[snd x])
   ; compose := λ x y z f g, (fst f ∘ fst g, snd f ∘ snd g)
  |}.

Notation "C × D" := (Product C D) (at level 40, left associativity) : category_scope.

