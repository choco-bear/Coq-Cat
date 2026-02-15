Require Import CommonTactics Category.
Require Export Functor.

Local Open Scope functor_scope.

Create HintDb functor_app discriminated.
Create HintDb functor_laws discriminated.
Create HintDb fmap_norm discriminated.

Global Hint Rewrite @Id_fobj @Id_fmap @Const_fobj @Const_fmap @Comp_fobj @Comp_fmap : functor_app.
Global Hint Rewrite @fmap_id @fmap_comp : fmap_norm.

Lemma functor_ext `{C : Category ObjC} `{D : Category ObjD} (F G : C ⟶ D)
  : fobj F = fobj G
  → (∀ x y (f : x ~> y), JMeq (F # f) (G # f))%morphism
  → F = G.
Proof.
  rewrite /fobj /fmap. depdes F G. intros <- eqFmap.
  assert (fmap = fmap0) as <- by hrepeat eapply func_ext_dep; i; try by apply JMeq_eq.
  f_equal; hrepeat eapply func_ext_dep; i; try apply proof_irr.
Qed.

Section FunctorLaws.
  Context `{C : Category ObjC} `{D : Category ObjD}.

  Lemma functor_id_left (F : C ⟶ D) : Id ∘ F = F.
  Proof. apply functor_ext; first apply func_ext; i; autorewrite with functor_app=> //. Qed.

  Lemma functor_id_right (F : C ⟶ D) : F ∘ Id = F.
  Proof. apply functor_ext; first apply func_ext; i; autorewrite with functor_app=> //. Qed.

  Lemma functor_comp_assoc (F : C ⟶ D) `(G : (B : Category ObjB) ⟶ C) `(H : (A : Category ObjA) ⟶ B)
    : F ∘ (G ∘ H) = F ∘ G ∘ H.
  Proof. apply functor_ext; first apply func_ext; i; autorewrite with functor_app=> //. Qed.
End FunctorLaws.
Global Hint Rewrite @functor_id_left @functor_id_right @functor_comp_assoc : functor_laws.


(** Tactics **)
Ltac functor_norm := autorewrite with functor_laws; autorewrite with functor_app; autorewrite with fmap_norm.
Tactic Notation "functor_norm" "in" hyp(H) := autorewrite with functor_laws in H; autorewrite with functor_app in H; autorewrite with fmap_norm in H.
Tactic Notation "functor_norm" "in" "*" "|-" := repeat_on_hyps (fun H => functor_norm in H).
Tactic Notation "functor_norm" "in" "*" := autorewrite with functor_laws in *; autorewrite with functor_app in *; autorewrite with fmap_norm in *.