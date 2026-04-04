Require Import CommonTactics CommonFacts Category CategoryTactics.
Require Import Functor FunctorTactics FunctorFacts.
Require Import Morphism MorphismTactics.

Local Open Scope morphism_scope.

Section IsIsomorphism.
  #[export]
  Program Instance Functor_preserves_IsIso `{C : Category ObjC} `{D : Category ObjD} (T : C ⟶ D) `(f : x ~{C}~> y) `{!IsIsomorphism f}
    : IsIsomorphism (T # f) := {| inverse_morphism := T # f⁻¹ |}.
  Next Obligation. rewrite -fmap_comp inv_morphism_left; common_simpl. Qed.
  Next Obligation. rewrite -fmap_comp inv_morphism_right; common_simpl. Qed.
End IsIsomorphism.

Section FunctorSimpl.
  Context `{C : Category ObjC} `{D : Category ObjD} (T : C ⟶ D).

  Lemma fmap_to_inv `(f : x ~{C}~> y) `{!IsIsomorphism f}
    : T # f⁻¹ = (T # f)⁻¹.
  Proof. common_simpl. Qed.
End FunctorSimpl.
Hint Rewrite @fmap_to_inv : functor_prep.

Section IsGroupoid.
  #[export]
  Instance BinaryProduct_preserves_IsGroupoid `[G : Category ObjG] `(!IsGroupoid G) `[H : Category ObjH] `(!IsGroupoid H) : IsGroupoid (G × H).
  Proof.
    construct. depdes x y f.
    construct; common_simpl.
  Qed.
End IsGroupoid.
