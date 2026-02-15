Require Import CommonTactics CommonFacts Category.
Require Export Functor.

Create HintDb functor_prep discriminated.   (* For preprocessing *)
Create HintDb functor_laws discriminated.   (* For operations between functors *)
Create HintDb functor_unfold discriminated. (* For unfolding fobj / fmap *)
Create HintDb functor_norm discriminated.   (* For normalizing the exprssions *)

Global Hint Rewrite @inv_functor_left @inv_functor_right : functor_laws.
Global Hint Rewrite @Id_fobj @Id_fmap @Const_fobj @Const_fmap @Comp_fobj @Comp_fmap : functor_unfold.
Global Hint Rewrite @fmap_id @fmap_comp : functor_norm.

Ltac functor_norm :=
  autorewrite with functor_prep;
  autorewrite with functor_laws;
  autorewrite with functor_unfold;
  autorewrite with functor_norm.
Tactic Notation "functor_norm" "/=" := functor_norm=> /=.
Tactic Notation "functor_norm" "//" := functor_norm=> //.
Tactic Notation "functor_norm" "//=" := functor_norm=> //=.
Tactic Notation "functor_norm" "in" hyp(H) :=
  autorewrite with functor_prep in H;
  autorewrite with functor_laws in H;
  autorewrite with functor_unfold in H;
  autorewrite with functor_norm in H.
Tactic Notation "functor_norm" "in" "*" :=
  autorewrite with functor_prep in *;
  autorewrite with functor_laws in *;
  autorewrite with functor_unfold in *;
  autorewrite with functor_norm in *.
Tactic Notation "functor_norm" "in" "*" "|-" := repeat_on_hyps (fun H => functor_norm in H).

Lemma functor_ext `{C : Category ObjC} `{D : Category ObjD} (F G : C ⟶ D)
  : fobj F = fobj G
  → (∀ x y (f : x ~> y), JMeq (F # f) (G # f))%morphism
  → F = G.
Proof.
  rewrite /fobj /fmap. depdes F G. intros <- eqFmap.
  assert (fmap = fmap0) as <- by hrepeat eapply func_ext_dep; i; try by apply JMeq_eq.
  f_equal; hrepeat eapply func_ext_dep; i; try apply proof_irr.
Qed.

Section FunctorPreps.
  Context `{B : Category ObjB} `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) (G : B ⟶ C).
  Local Open Scope functor_scope.

  Lemma functor_prep_compose_fobj x : F (G x) = (F ∘ G) x.
  Proof. rewrite Comp_fobj //. Qed.

  Lemma functor_prep_compose_fmap {x y : ObjB} (f : x ~> y) : F # G # f =[D] (F ∘ G) # f.
  Proof. rewrite Comp_fmap //. Qed.
End FunctorPreps.
Global Hint Rewrite @functor_prep_compose_fobj @functor_prep_compose_fmap : functor_prep.

Section FunctorLaws.
  Context `{C : Category ObjC} `{D : Category ObjD}.
  Local Open Scope functor_scope.

  Lemma functor_id_left (F : C ⟶ D) : Id ∘ F = F.
  Proof. apply functor_ext; first apply func_ext; i; functor_norm //. Qed.

  Lemma functor_id_right (F : C ⟶ D) : F ∘ Id = F.
  Proof. apply functor_ext; first apply func_ext; i; functor_norm //. Qed.

  Lemma functor_comp_assoc (F : C ⟶ D) `(G : (B : Category ObjB) ⟶ C) `(H : (A : Category ObjA) ⟶ B)
    : F ∘ (G ∘ H) = F ∘ G ∘ H.
  Proof. apply functor_ext; first apply func_ext; i; functor_norm //. Qed.
End FunctorLaws.
Global Hint Rewrite @functor_id_left @functor_id_right @functor_comp_assoc : functor_laws.

Section Inverses.
  Context `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F}.
  Local Open Scope functor_scope.

  Lemma functor_inv_norm_1 `{B : Category ObjB} (G : D ⟶ B) : G ∘ F ∘ F⁻¹ = G.
  Proof. rewrite -functor_comp_assoc inv_functor_right functor_id_right //. Qed.

  Lemma functor_inv_norm_2 `{B : Category ObjB} (G : C ⟶ B) : G ∘ F⁻¹ ∘ F = G.
  Proof. rewrite -functor_comp_assoc inv_functor_left functor_id_right //. Qed.
  
  Global Program Instance isomorphism_fobj_bijective
    : Bijective (fobj F) := {| inverse_function := fobj F⁻¹ |}.
  Solve Obligations with by rewrite <-Comp_fobj; functor_norm.

  Lemma inverse_functor_fobj : fobj F⁻¹ = (F⁻¹)%function.
  Proof. reflexivity. Qed.
End Inverses.
Global Hint Rewrite @functor_inv_norm_1 @functor_inv_norm_2 : functor_laws.
Global Hint Rewrite @inverse_functor_fobj : functor_unfold.
Global Hint Rewrite <- @inverse_functor_fobj : functor_prep.