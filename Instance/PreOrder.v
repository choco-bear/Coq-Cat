Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** Any pre-ordered set forms a category. *)
Program Definition PreOrderSet `(PRE : @PreOrder X R) : Category :=
  {| obj := X
   ; hom := R
   ; homset := (* Since there can be at most one morphism between any two
                * objects, multiple morphisms of the same type are equal. *)
        λ x y, {| equiv := λ _ _, True |}
   ; id := λ x, @reflexivity X R (@PreOrder_Reflexive X R PRE) x
   ; compose :=
        λ x y z f g, @transitivity X R (@PreOrder_Transitive X R PRE) x y z g f
  |}.

Coercion PreOrderSet : PreOrder >-> Category.