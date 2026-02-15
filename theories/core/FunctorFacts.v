Require Import Common CommonTactics Category Functor FunctorTactics.

Local Open Scope functor_scope.

Global Program Instance iso_functor_fully_faithful
  `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F} : FullyFaithful F.
Next Obligation. construct. fmap F⁻¹ in H. fmap_eq_simplify //. Qed.
Next Obligation. construct. unshelve eexists (⇑(F⁻¹ # _))%morphism; try fmap_eq_simplify; functor_norm //. Qed.