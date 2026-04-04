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

Section MorphismProperties.
  Context `{C : Category Obj} `(f : x ~> y).

  Program Instance has_retraction_monic (r : RetractionOf f) : Monic f.
  Next Obligation. comp_l r in H. rewrite retr_left_inv in H. common_simpl. Qed.

  Program Instance has_section_epic (s : SectionOf f) : Epic f.
  Next Obligation. cby comp_r (f ∘ s); rewrite ?H ?sect_right_inv. Qed.

  Program Instance monic_comp `{!Monic f} `(g : z ~> x) `{!Monic g} : Monic (f ∘ g).
  Next Obligation. rewrite -!comp_assoc in H. hrepeat apply monic in H; ss. Qed.

  Program Definition monic_strip `(g : z ~> x) `{!Monic (f ∘ g)} : Monic g := _.
  Next Obligation. construct. comp_l f in H. apply monic in H; ss. Qed.

  Program Instance epic_comp `{!Epic f} `(g : z ~> x) `{!Epic g} : Epic (f ∘ g).
  Next Obligation. rewrite !comp_assoc in H. hrepeat apply epic in H; ss. Qed.

  Program Definition epic_strip `(g : z ~> x) `{!Epic (f ∘ g)} : Epic f := _.
  Next Obligation. construct. comp_r g in H. rewrite -!comp_assoc in H. apply epic in H; ss. Qed.
End MorphismProperties.