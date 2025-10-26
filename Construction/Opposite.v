Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The opposite category [C^op] of [C] is the category whose objects are the same
  * as those of [C], but whose morphisms are reversed.
  *)
Program Definition OppositeCategory (C : Category) : Category :=
  {| obj := @obj C
   ; hom := λ x y, @hom C y x
   ; homset := λ x y, @homset C y x
   ; id := λ x, @id C x
   ; compose := λ x y z f g, g ∘ f
  |}.

Notation "C '^op'" := (OppositeCategory C) (at level 0, format "C '^op'") : category_scope.

(** The opposite functor [F^op] of a functor [F : C ⟶ D] is the functor from [C^op]
  * to [D^op] defined by the same action on objects and morphisms as [F].
  *)
Program Definition Opposite_Functor {C D : Category} (F : C ⟶ D) : C^op ⟶ D^op :=
  {| fobj := λ x, F x
   ; fmap := λ x y f, fmap[F] f
  |}.
Next Obligation. proper. now rewrites. Qed.
Next Obligation. exact (fmap_comp _ _). Qed.

Notation "F '^op'" := (Opposite_Functor F)
  (at level 0, format "F '^op'") : functor_scope.