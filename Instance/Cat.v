Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** The category [Cat] is a category, whose objects are categories, and whose
  * morphisms are functors. *)
Program Definition Cat : Category :=
  {| obj := Category
   ; hom := λ C D, C ⟶ D
   ; homset := λ C D, @ob_setoid Fun[C,D]
   ; id := λ C, Id[C]
   ; compose := @Functor_Compose

   ; compose_respects := @Functor_Compose_respects

   ; id_left := λ C D F, Functor_Compose_Id_left F
   ; id_right := λ C D F, Functor_Compose_Id_right F

   ; comp_assoc := λ B C D E F G H,
       Functor_Compose_Assoc F G H
   ; comp_assoc_sym := λ B C D E F G H,
       Functor_Compose_Assoc_Sym F G H
  |}.