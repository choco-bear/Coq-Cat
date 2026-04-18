Require Import CommonTactics CommonFacts Category CategoryTactics.

Section Morphisms.
  Context `{C : Category Obj}.
  Local Open Scope morphism_scope.

  Lemma id_morphism_unique [x : Obj] (f : x ~> x)
    : (∀ (y : Obj) (g : y ~> x), f ∘ g = g)
    → (∀ (y : Obj) (g : x ~> y), g ∘ f = g)
    → f = id.
  Proof. i. cut (f ∘ id[x] = id[x]); common_simpl. Qed.
End Morphisms.

Section BinaryProduct.
  Context `{C : Category ObjC} `{D : Category ObjD}.

  #[export]
  Instance BinaryProduct_preserves_IsMonoid `(!IsMonoid C) `(!IsMonoid D) : IsMonoid (C × D).
  Proof. repeat construct; ss; common_simpl. Qed.
  
  #[export]
  Program Instance BinaryProduct_preserves_IsDiscrete `{!IsDiscrete C} `{!IsDiscrete D} : IsDiscrete (C × D).
End BinaryProduct.