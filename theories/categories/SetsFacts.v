Require Import Common Sets Functor.

Global Instance endofunctor_fmap (F : Sets ⟶ Sets) : FMap F := λ _ _ f, (F # f)%morphism.