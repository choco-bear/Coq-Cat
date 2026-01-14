Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** Provides the hom functor for a given object in a category. *)
Section Hom.
  Context {C : Category}.

  Program Definition HomBiFunctor : C^op × C ⟶ Sets :=
    {|  fobj :=
          λ p : obj[C^op × C],
            match p return obj[Sets] with
            | (x,y) => {| carrier := hom[C] x y 
                        ; is_setoid := @homset C x y
                       |}
            end
      ; fmap := λ`(x1,y1) : obj[C^op × C],
                λ`(x2,y2) : obj[C^op × C],
                λ`(f,g) : (x1,y1) ~{C^op × C}~> (x2,y2),
                  {| morphism := λ X, g ∘ X ∘ f |}
    |}.
  
  Program Definition HomFunctor (x : C) : C ⟶ Sets :=
    HomBiFunctor ◯ (Const (x : C^op) × Id[C]).

  Program Definition HomFunctor_op (y : C) : C^op ⟶ Sets :=
    HomBiFunctor ◯ (Id[C^op] × Const y).
End Hom.

Arguments HomFunctor {_%_category_scope} {_%_object_scope}.
Arguments HomFunctor_op {_%_category_scope} {_%_object_scope}.

Notation "'Hom(-,-)'" := (@HomBiFunctor _) (at level 9) : functor_scope.
Notation "'Hom[' C '](-,-)'" := (@HomBiFunctor C)
  (at level 9, only parsing) : functor_scope.

Notation "'Hom(' x ',-)'" := (@HomFunctor _ x%object)
  (at level 9, format "Hom( x ,-)") : functor_scope.
Notation "'Hom[' C '](' x ',-)'" := (@HomFunctor C%category x%object)
  (at level 9, only parsing) : functor_scope.

Notation "'Hom(-,' y ')'" := (@HomFunctor_op _ y%object)
  (at level 9, format "Hom(-, y )") : functor_scope.
Notation "'Hom[' C '](-,' y ')'" := (@HomFunctor_op C%category y%object)
  (at level 9, only parsing) : functor_scope.