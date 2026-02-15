Require Import Common CommonTactics Category Functor FunctorTactics.

Local Open Scope functor_scope.

Lemma fmap_JMeq `{C : Category ObjC} `{D : Category ObjD} (F G : C ⟶ D)
  : ∀ (EQ : F = G) x y (f : x ~> y), (JMeq (F # f) (G # f))%morphism.
Proof. rewrite /fmap. i. depdes F G. inv EQ. by apply inj_pair2 in H1 as ->. Qed.

Lemma fmap_JMeq_JMeq `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D)
  : ∀ x y (f : x ~> y) x' y' (g : x' ~> y') (eqx : x' = x) (eqy : y' = y),
    f = hom_cast eqx eqy g → (JMeq (F # f) (F # g))%morphism.
Proof. rewrite /fmap. i. depdes F. subst. by rewrite hom_cast_eq. Qed.

Global Program Instance iso_functor_fully_faithful
  `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F} : FullyFaithful F.
Next Obligation. fmap F⁻¹ in H. fmap_eq_simplify //. Qed.
Next Obligation.
  eexists (⇑(F⁻¹ # h))%morphism.
  duplicate_goal.
  { fmap_eq_simplify. (* cannot address the hom_cast in the goal! *)
    (* TODO: we should be able to address the hom_cast in the hypotheses/goal. *)
    admit. } 
  eapply JMeq_eq. etransitivity; first eapply fmap_JMeq_JMeq=> //.
  autorewrite with functor_prep. eapply (fmap_JMeq (F ∘ F⁻¹) Id).
  Unshelve. all: functor_norm //.
Admitted.