Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.

Generalizable All Variables.

(** Being given two categories [C] and [D], functors from [C] to [D] form a
  * category, whose objects are functors, and whose morphisms are natural
  * transformations.
  *)
Program Definition Fun (C : Category) (D : Category) : Category :=
  {| obj := C ⟶ D
   ; hom := λ F G, F ⟹ G
   ; homset := λ F G, NaturalTransform_Setoid
   ; id := @NaturalTransform_id _ _
   ; compose := @NaturalTransform_compose _ _

   ; compose_respects := @NaturalTransform_compose_respects _ _

   ; id_left := λ F G η x, id_left (η x)
   ; id_right := λ F G η x, id_right (η x)

   ; comp_assoc := λ F G H K η μ ν x,
       comp_assoc (η x) (μ x) (ν x)
   ; comp_assoc_sym := λ F G H K η μ ν x,
       comp_assoc_sym (η x) (μ x) (ν x)
  |}.