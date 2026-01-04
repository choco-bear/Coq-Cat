Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** This is the discrete category. A category is said to be discrete when every
  * morphism is an identity. Every type [A] is the type of objects of a discrete
  * category (just add one identity morphism [x ~> x] for each [x : A]), and every
  * discrete category is so determined by its set of objects. *)
Program Definition DiscreteCat (A : Type) : Category :=
  {| obj := A
   ; hom := λ x y, x = y
   ; homset := (* Since there can be at most one morphism between any two objects,
                * multiple morphisms of the same type are equal. *)
        λ x y, {| equiv := λ _ _, poly_unit |}
   ; id := λ x, eq_refl x
   ; compose := λ x y z (f : y = z) (g : x = y), eq_ind_r (λ t, t = z) f g
  |}.

Notation "'Cat[' A ']'" := (DiscreteCat A%type)
  (at level 9, format "Cat[ A ]") : category_scope.

#[export]
Instance Discrete_IsSet (A : Type) : IsSet Cat[A].
Proof. by split; construct. Qed.