Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** Provides the hom functor for a given object in a category. *)
Section Hom.
  Context {C : Category}.

  Program Definition HomFunctor (x : C) : C ⟶ Sets :=
    {| fobj := λ y, {| carrier := hom x y
                     ; is_setoid := homset x y
                    |}
     ; fmap := λ _ _ f, {| morphism := λ g, f ∘ g |}
    |}.

  Program Definition HomFunctor_op (y : C) : C^op ⟶ Sets :=
    {| fobj := λ x, {| carrier := @hom C x y
                     ; is_setoid := @homset C x y
                    |}
     ; fmap := λ _ _ f, {| morphism := λ g, g ∘ f |}
    |}.
End Hom.

Arguments HomFunctor {_%_category_scope} {_%_object_scope}.
Arguments HomFunctor_op {_%_category_scope} {_%_object_scope}.

Notation "'Hom(' x ',-)'" := (@HomFunctor _ x%object)
  (at level 9, format "Hom( x ,-)") : functor_scope.
Notation "'Hom[' C '](' x ',-)'" := (@HomFunctor C%category x%object)
  (at level 9, only parsing) : functor_scope.

Notation "'Hom(-,' y ')'" := (@HomFunctor_op _ y%object)
  (at level 9, format "Hom(-, y )") : functor_scope.
Notation "'Hom[' C '](-,' y ')'" := (@HomFunctor_op C%category y%object)
  (at level 9, only parsing) : functor_scope.