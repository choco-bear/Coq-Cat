Require Import CommonTactics CommonFacts Category.
Require Import Functor FunctorTactics FunctorFacts.
Require Import Morphism MorphismTactics.

Program Instance Functor_preserves_IsIso `{C : Category ObjC} `{D : Category ObjD} (T : C ⟶ D) `(g : x ~{C}~> y) `{!IsIsomorphism g}
  : IsIsomorphism (T # g) := {| inverse_morphism := T # g⁻¹ |}.
Next Obligation. rewrite -fmap_comp inv_morphism_left; common_simpl. Qed.
Next Obligation. rewrite -fmap_comp inv_morphism_right; common_simpl. Qed.