Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.
Require Import Category.Construction.Fun.

Generalizable All Variables.

(** The one category, with one object, one morphism. Also called the trivial
  * category or singleton category.
  *)

Program Definition _1 : Category := 
  {| obj := poly_unit
   ; hom := fun _ _ => poly_unit
   ; homset := Morphism_equality
   ; id := fun _ => ttt
   ; compose := fun _ _ _ _ _ => ttt
  |}.

Notation "1" := _1 : category_scope.

(** The unique functor to one category from any other category. *)
Program Definition Erase `(C : Category) : C ⟶ 1 :=
  {| fobj := fun _ => ttt
   ; fmap := fun _ _ _ => id
  |}.