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

#[export]
Instance BinaryProduct_preserves_IsMonoid `[M : Category ObjM] `(!IsMonoid M) `[N : Category ObjN] `(!IsMonoid N) : IsMonoid (M × N).
Proof. repeat construct; common_simpl. Qed.