Require Import CommonTactics CommonFacts Category.
Require Export Functor.

Create HintDb functor_prep discriminated.   (* For preprocessing *)
Create HintDb functor_laws discriminated.   (* For operations between functors *)
Create HintDb functor_unfold discriminated. (* For unfolding fobj / fmap *)
Create HintDb functor_norm discriminated.   (* For normalizing the exprssions *)

Global Hint Rewrite @inv_functor_left @inv_functor_right : functor_laws.
Global Hint Rewrite @Id_fobj @Id_fmap @Const_fobj @Const_fmap @Comp_fobj @Comp_fmap
                    @Paring_fobj @Paring_fmap @Fst_fobj @Fst_fmap @Snd_fobj @Snd_fmap : functor_unfold.
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

Tactic Notation "functor_done" tactic(tac) := solve [program_simpl; functor_norm in *; common_simpl; tac].
Tactic Notation "functor_done" := functor_done done.

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
Global Hint Rewrite <- @Comp_fobj @Comp_fmap : functor_prep.

Section FunctorLaws.
  Context `{C : Category ObjC} `{D : Category ObjD}.
  Local Open Scope functor_scope.

  Lemma functor_id_left (F : C ⟶ D) : id ∘ F = F.
  Proof. apply functor_ext; first apply func_ext; i; functor_norm //. Qed.

  Lemma functor_id_right (F : C ⟶ D) : F ∘ id = F.
  Proof. apply functor_ext; first apply func_ext; i; functor_norm //. Qed.

  Lemma functor_comp_assoc (F : C ⟶ D) `(G : (B : Category ObjB) ⟶ C) `(H : (A : Category ObjA) ⟶ B)
    : F ∘ (G ∘ H) = F ∘ G ∘ H.
  Proof. apply functor_ext; first apply func_ext; i; functor_norm //. Qed.
End FunctorLaws.
Global Hint Rewrite @functor_id_left @functor_id_right @functor_comp_assoc : functor_laws.

Section InverseNorm.
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
End InverseNorm.
Global Hint Rewrite @functor_inv_norm_1 @functor_inv_norm_2 : functor_laws.
Global Hint Rewrite @inverse_functor_fobj : functor_unfold.
Global Hint Rewrite <- @inverse_functor_fobj : functor_prep.

Section IsoFunctorInstances.
  Global Program Instance iso_functor_compose_iso `{B : Category ObjB} `{C : Category Obj} `{D : Category ObjD}
    (F : C ⟶ D) `{!IsFunctorIso F} (G : B ⟶ C) `{!IsFunctorIso G} : IsFunctorIso (F ∘ G) | 30 :=
    {| inverse_functor := G⁻¹ ∘ F⁻¹ |}.
  Solve Obligations with ii; functor_norm //.

  Global Program Instance id_functor_iso `{C : Category Obj}
    : IsFunctorIso id[C] := {| inverse_functor := id |}.
  Solve Obligations with ii; functor_norm //.

  Global Program Instance inv_functor_iso `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F}
    : IsFunctorIso F⁻¹ | 10 := {| inverse_functor := F |}.
  Solve Obligations with ii; functor_norm //.

  Lemma comp_inv `{B : Category ObjB} `{C : Category Obj} `{D : Category ObjD}
    (F : C ⟶ D) `{!IsFunctorIso F} (G : B ⟶ C) `{!IsFunctorIso G}
    : ((F ∘ G)⁻¹ = G⁻¹ ∘ F⁻¹)%functor.
  Proof. ss. Qed.

  Lemma inv_involutive `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) `{!IsFunctorIso F} : (F⁻¹)⁻¹ = F.
  Proof. ss. Qed.

  Lemma id_inv_id `{C : Category Obj} : (id[C]⁻¹ = id[C])%functor.
  Proof. ss. Qed.
End IsoFunctorInstances.
Global Hint Rewrite @comp_inv @inv_involutive @id_inv_id : functor_laws.

Section FunctorJMeqCast.
  Local Open Scope morphism_scope.

  Lemma eq_to_jm {A} {x y : A} : x = y -> JMeq x y.
  Proof. intros ->. apply JMeq_refl. Qed.

  Lemma jm_to_eq {A} {x y : A} : JMeq x y -> x = y.
  Proof. apply JMeq_eq. Qed.

  Lemma jmeq_downcast_lhs `{C : Category ObjC} {x1 y1 x1' y1' x2 y2 : ObjC}
    (f : x1 ~> y1) (g : x2 ~> y2) (eqx : x1 = x1') (eqy : y1 = y1')
    : JMeq (hom_cast eqx eqy f) g → JMeq f g.
  Proof. depdes eqx eqy. rewrite hom_cast_eq //. Qed.

  Lemma jmeq_downcast_rhs `{C : Category ObjC} {x1 y1 x2 y2 x2' y2' : ObjC}
    (f : x1 ~> y1) (g : x2 ~> y2) (eqx : x2 = x2') (eqy : y2 = y2')
    : JMeq f (hom_cast eqx eqy g) → JMeq f g.
  Proof. depdes eqx eqy. rewrite hom_cast_eq //. Qed.

  Lemma jmeq_upcast_lhs `{C : Category ObjC} {x1 y1 x1' y1' x2 y2 : ObjC}
    (f : x1 ~> y1) (g : x2 ~> y2) (eqx : x1 = x1') (eqy : y1 = y1')
    : JMeq f g → JMeq (hom_cast eqx eqy f) g.
  Proof. depdes eqx eqy. rewrite hom_cast_eq //. Qed.

  Lemma jmeq_upcast_rhs `{C : Category ObjC} {x1 y1 x2 y2 x2' y2' : ObjC}
    (f : x1 ~> y1) (g : x2 ~> y2) (eqx : x2 = x2') (eqy : y2 = y2')
    : JMeq f g → JMeq f (hom_cast eqx eqy g).
  Proof. depdes eqx eqy. rewrite hom_cast_eq //. Qed.

  Lemma jmeq_subst_lhs `{C : Category ObjC} `{D : Category ObjD} (F1 F1' F2 : C ⟶ D)
    {x1 y1 x2 y2 : ObjC} (f : x1 ~> y1) (g : x2 ~> y2)
    : JMeq (F1 # f) (F2 # g) -> F1 = F1' -> JMeq (F1' # f) (F2 # g).
  Proof. by i; subst. Qed.

  Lemma jmeq_subst_rhs `{C : Category ObjC} `{D : Category ObjD} (F1 F2 F2' : C ⟶ D)
    {x1 y1 x2 y2 : ObjC} (f : x1 ~> y1) (g : x2 ~> y2)
    : JMeq (F1 # f) (F2 # g) -> F2 = F2' -> JMeq (F1 # f) (F2' # g).
  Proof. by i; subst. Qed.
End FunctorJMeqCast.

Section HomCastBubble.
  Context `{C : Category ObjC}.
  Local Open Scope morphism_scope.

  Lemma hom_cast_id {x y : ObjC} (eq1 eq2 : x = y) : hom_cast eq1 eq2 id[x] = id[y].
  Proof. depdes eq1 eq2. rewrite hom_cast_eq //. Qed.

  Lemma hom_cast_comp {x1 y1 z1 x2 y2 z2 : ObjC}
    (eqy1 : y1 = y2) (eqy2 : y1 = y2) (eqz : z1 = z2) (eqx : x1 = x2)
    (f : y1 ~> z1) (g : x1 ~> y1) :
    hom_cast eqy1 eqz f ∘ hom_cast eqx eqy2 g = hom_cast eqx eqz (f ∘ g).
  Proof. assert (eqy1 = eqy2) as -> by apply proof_irr. depdes eqx eqy2 eqz. rewrite !hom_cast_eq //. Qed.

  Lemma hom_cast_comp_left {x y z z' : ObjC} (eqz : z = z') (f : y ~> z) (g : x ~> y) :
    hom_cast eq_refl eqz f ∘ g = hom_cast eq_refl eqz (f ∘ g).
  Proof. depdes eqz. rewrite !hom_cast_eq //. Qed.

  Lemma hom_cast_comp_right {x y z x' : ObjC} (eqx : x = x') (f : y ~> z) (g : x ~> y) :
    f ∘ hom_cast eqx eq_refl g = hom_cast eqx eq_refl (f ∘ g).
  Proof. depdes eqx. rewrite !hom_cast_eq //. Qed.

  Context `{D : Category ObjD}.

  Lemma hom_cast_fmap (F : C ⟶ D) {x y x' y' : ObjC}
    (eqx : x = x') (eqy : y = y') (f : x ~> y) :
    F # hom_cast eqx eqy f = hom_cast (fapply F eqx) (fapply F eqy) (F # f).
  Proof. depdes eqx eqy. rewrite !hom_cast_eq //. Qed.
End HomCastBubble.
Global Hint Rewrite @hom_cast_comp @hom_cast_comp_left @hom_cast_comp_right @hom_cast_fmap : functor_prep.

Ltac fmap_eq_simplify_prep :=
  tryif (do ! match goal with
  | [ H : (?F1 # ?f1)%morphism = (?F2 # ?f2)%morphism |- _ ] => apply eq_to_jm in H
  | [|- (?F1 # ?f1)%morphism = (?F2 # ?f2)%morphism ] => apply jm_to_eq
  | [|- ?f = ?g ] =>
      match type of (f : _ ~> _) with
      | ?x ~> ?y =>
          let EQ := fresh "EQ" in let MORPHISM := fresh "MORPHISM" in let HeqMORPHISM := fresh "HeqMORPHISM" in
          assert (EQ : f = (id # f)%morphism) by reflexivity;
          remember f as MORPHISM eqn:HeqMORPHISM;
          rewrite EQ; clear EQ; subst MORPHISM
      end; match type of (g : _ ~> _) with
      | ?x ~> ?y =>
          let EQ := fresh "EQ" in let MORPHISM := fresh "MORPHISM" in let HeqMORPHISM := fresh "HeqMORPHISM" in
          assert (EQ : g = (id # g)%morphism) by reflexivity;
          remember g as MORPHISM eqn:HeqMORPHISM;
          rewrite EQ; clear EQ; subst MORPHISM
      end
  end) then ( autorewrite with functor_prep in * ) else (
  match goal with
  | [|- JMeq ?f ?g ] => autorewrite with functor_prep in *
  | [ H : JMeq (?F1 # ?f1)%morphism (?F2 # ?f2)%morphism |- _ ] => autorewrite with functor_prep in *
  | _ => fail "No morphism equalities found"
  end).

Ltac fmap_eq_simplify_proc :=
  repeat match goal with
  | [|- JMeq (⇑ ?f)%morphism ?g ] =>
      eapply jmeq_upcast_lhs
  | [|- JMeq ?f (⇑ ?g)%morphism ] =>
      eapply jmeq_upcast_rhs
  | [ H : JMeq (⇑ ?f)%morphism ?g |- _ ] =>
      eapply jmeq_downcast_lhs in H
  | [ H : JMeq ?f (⇑ ?g)%morphism |- _ ] =>
      eapply jmeq_downcast_rhs in H
  | [ H : JMeq (?F1 # ?f1)%morphism (?F2 # ?f2)%morphism |- _ ] =>
      let EQ := fresh "EQ" in
      eassert (EQ : F1 = _); first progress autorewrite with functor_laws; first reflexivity;
      match type of EQ with
      | F1 = ?F => eapply (jmeq_subst_lhs F1 F F2 f1 f2) in H; [|exact EQ]
      end; clear EQ
  | [ H : JMeq (?F1 # ?f1)%morphism (?F2 # ?f2)%morphism |- _ ] =>
      let EQ := fresh "EQ" in
      eassert (EQ : F2 = _); first progress autorewrite with functor_laws; first reflexivity;
      match type of EQ with
      | F2 = ?F => eapply (jmeq_subst_rhs F1 F2 F f1 f2) in H; [|exact EQ]
      end; clear EQ
  | [|- JMeq (?F1 # ?f1)%morphism (?F2 # ?f2)%morphism] =>
      let EQ := fresh "EQ" in
      eassert (EQ : _ = F1); first progress autorewrite with functor_laws; first reflexivity;
      match type of EQ with
      | ?F = F1 => eapply (jmeq_subst_lhs F F1 F2 f1 f2); [|exact EQ]
      end; clear EQ
  | [|- JMeq (?F1 # ?f1)%morphism (?F2 # ?f2)%morphism] =>
      let EQ := fresh "EQ" in
      eassert (EQ : _ = F2); first progress autorewrite with functor_laws; first reflexivity;
      match type of EQ with
      | ?F = F2 => eapply (jmeq_subst_rhs F1 F F2 f1 f2); [|exact EQ]
      end; clear EQ
  | _ => progress autorewrite with functor_prep in *
  end.

Ltac fmap_eq_simplify_final :=
  repeat match goal with
  | [ H : @JMeq (Arrow _ _) _ (Arrow _ _) _ |- _ ] => apply jm_to_eq in H
  | [|- @JMeq (Arrow _ _) _ (Arrow _ _) _ ] => apply eq_to_jm
  end.

Ltac fmap_eq_simplify := fmap_eq_simplify_prep; fmap_eq_simplify_proc; fmap_eq_simplify_final.
Tactic Notation "fmap_eq_simplify" "//" := fmap_eq_simplify; common_simpl.
Tactic Notation "fmap_eq_simplify" "/=" := fmap_eq_simplify; try functor_done.
Tactic Notation "fmap_eq_simplify" "//=" := fmap_eq_simplify; common_simpl; try functor_done.

Tactic Notation "fmap" constr(F) "in" hyp(H) := eapply (fapply (fmap F)) in H.
Tactic Notation "fmap" constr(F) "in" hyp(H) "as" ident(name) := eapply (fapply (fmap F)) in H as name.

Tactic Notation "functor_solver" tactic(tac) := program_simpl; functor_norm in *; common_simpl; solve [done | fmap_eq_simplify; common_simpl; try functor_done tac].
Tactic Notation "functor_solver" := functor_solver done.