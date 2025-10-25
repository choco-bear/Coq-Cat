Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The one category, with one object, one morphism. Also called the trivial
  * category or singleton category.
  *)

Program Definition _1@{o h p} : Category@{o h p} := 
  {| obj := poly_unit@{o}
   ; hom := fun _ _ => poly_unit@{h}
   ; homset := Morphism_equality
   ; id := fun _ => ttt
   ; compose := fun _ _ _ _ _ => ttt
  |}.
Next Obligation. now destruct f. Qed.
Next Obligation. now destruct f. Qed.

Notation "1" := _1 : category_scope.

(** The unique functor to one category from any other category. *)
#[export]
Program Instance Erase `(C : Category) : C ⟶ 1 :=
  {| fobj := fun _ => ttt
   ; fmap := fun _ _ _ => id
  |}.