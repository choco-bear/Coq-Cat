Require Import Common CommonTactics Category Functor FunctorTactics.

Local Open Scope functor_scope.

Global Program Instance iso_functor_fully_faithful
  `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F} : FullyFaithful F.
Next Obligation. construct. fmap F⁻¹ in H. fmap_eq_simplify //. Qed.
Next Obligation. construct. unshelve eexists (⇑(F⁻¹ # _))%morphism; try fmap_eq_simplify; functor_norm //. Qed.

Section InverseUnique.
  Context `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F} (G : D ⟶ C).
  Local Open Scope functor_scope.

  Lemma functor_inv_left_unique : G ∘ F = Id → G = F⁻¹.
  Proof. i; transitivity (G ∘ F ∘ F⁻¹); last rewrite H; functor_norm //. Qed.

  Lemma functor_inv_right_unique : F ∘ G = Id → G = F⁻¹.
  Proof. i; transitivity (F⁻¹ ∘ F ∘ G); last rewrite -functor_comp_assoc H; functor_norm //. Qed.
End InverseUnique.