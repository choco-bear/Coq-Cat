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
   ; homset := λ x y, {| equiv := λ _ _, x = y |}
   ; id := λ x, eq_refl x
   ; compose := λ x y z (f : y = z) (g : x = y), eq_ind_r (λ t, t = z) f g
  |}.