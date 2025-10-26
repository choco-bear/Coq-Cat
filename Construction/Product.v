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

   ; compose_respects := λ x y z f g fg h i hi,
        ( compose_respects (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi)
        , compose_respects (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi) )

   ; id_left := λ x y f,
        ( id_left (fst f)
        , id_left (snd f) )
   ; id_right := λ x y f,
        ( id_right (fst f)
        , id_right (snd f) )

   ; comp_assoc := λ x y z w f g h,
        ( comp_assoc (fst f) (fst g) (fst h)
        , comp_assoc (snd f) (snd g) (snd h) )
   ; comp_assoc_sym := λ x y z w f g h,
        ( comp_assoc_sym (fst f) (fst g) (fst h)
        , comp_assoc_sym (snd f) (snd g) (snd h) )
  |}.

Notation "C × D" := (Product C D) (at level 40, left associativity) : category_scope.

