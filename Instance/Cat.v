Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.Setoid.

Generalizable All Variables.

(** The category [Cat] is a category, whose objects are categories, and whose
  * morphisms are functors. *)
Program Definition Cat : Category :=
  {| obj := Category
   ; hom := @Functor
   ; homset := @Functor_Setoid
   ; id := @Functor_Identity
   ; compose := @Functor_Compose

   ; compose_respects := @Functor_Compose_respects

   ; id_left := @Functor_Compose_Id_left
   ; id_right := @Functor_Compose_Id_right

   ; comp_assoc := @Functor_Compose_Assoc
   ; comp_assoc_sym := @Functor_Compose_Assoc_Sym
  |}.