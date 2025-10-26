Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The opposite category [C^op] of [C] is the category whose objects are the same
  * as those of [C], but whose morphisms are reversed.
  *)
Program Definition Opposite (C : Category) : Category :=
  {| obj := @obj C
   ; hom := λ x y, @hom C y x
   ; homset := λ x y, @homset C y x
   ; id := λ x, @id C x
   ; compose := λ x y z f g, g ∘ f
   
   ; compose_respects := λ x y z f g fg h i hi,
        @compose_respects C z y x h i hi f g fg

   ; id_left := λ x y f, @id_right C y x f
   ; id_right := λ x y f, @id_left C y x f

   ; comp_assoc := λ x y z w f g h,
        @comp_assoc_sym C w z y x h g f
   ; comp_assoc_sym := λ x y z w f g h,
        @comp_assoc C w z y x h g f
  |}.

Notation "C '^op'" := (Opposite C)
  (at level 0, format "C '^op'") : category_scope.

Lemma op_invol {C : Category} : (C^op)^op = C.
Proof. unfold Opposite; destruct C; simpl. f_equal. Qed.

Definition op   {C : Category} {x y} (f : y ~{C}~> x) : x ~{C^op}~> y := f.
Definition unop {C : Category} {x y} (f : x ~{C^op}~> y) : y ~{C}~> x := f.