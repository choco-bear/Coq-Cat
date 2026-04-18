Require Import CommonTactics.

Class Bijective [A B : Type] (f : A → B) :=
  {
    inverse_function : B → A;
    bijective_inv_left : inverse_function ∘ f = Datatypes.id;
    bijective_inv_right : f ∘ inverse_function = Datatypes.id;
  }. 
Arguments inverse_function [A B]%_type_scope f%_function_scope {BIJECTIVE} _ : rename, simpl never.
  
Notation "f '⁻¹'" := (inverse_function f) (at level 7, left associativity, format "f ⁻¹") : function_scope.

Section Inverses.
  Context [A B : Type] (f : A → B) `{!Bijective f}.

  Lemma inv_left_pointwise x : f⁻¹ (f x) = x.
  Proof. transitivity ((f⁻¹ ∘ f) x)=> //. rewrite bijective_inv_left=> //. Qed.

  Lemma inv_right_pointwise x : f (f⁻¹ x) = x.
  Proof. transitivity ((f ∘ f⁻¹) x)=> //. rewrite bijective_inv_right=> //. Qed.

  Lemma inv_spec x y : y = f x → f⁻¹ y = x.
  Proof. intros ->. apply inv_left_pointwise. Qed.

  Lemma inv_normalize_1 [C : Type] (g : B → C) : g ∘ f ∘ f⁻¹ = g.
  Proof. extensionalities=> /=. rewrite inv_right_pointwise //. Qed.

  Lemma inv_normalize_2 [C : Type] (g : A → C) : g ∘ f⁻¹ ∘ f = g.
  Proof. extensionalities=> /=. rewrite inv_left_pointwise //. Qed.
End Inverses.
Global Hint Rewrite @bijective_inv_left @bijective_inv_right @inv_left_pointwise @inv_right_pointwise
                    @inv_spec @inv_normalize_1 @inv_normalize_2 : normalize.

Section ProofIrrel.
  Global Instance prop_pi (P : Prop) : ProofIrrel P.
  Proof. ii. apply proof_irr. Qed.

  Global Instance func_pi {A : Type} `{!ProofIrrel B} : ProofIrrel (A → B).
  Proof. ii. apply func_ext=> //. Qed.

  Global Instance func_pi_dep {A : Type} `{!(∀ a : A, ProofIrrel (B a))} : ProofIrrel (∀ a, B a).
  Proof. ii. apply func_ext_dep. i. apply proof_irrel. Qed.
End ProofIrrel.

Section Inhabited.
  Global Instance func_inhabited_dep {A : Type} `{!(∀ a : A, Inhabited (B a))} : Inhabited (∀ a, B a).
  Proof. split. i. exact inhabitant. Qed.
End Inhabited.

Section Unique.
  Global Program Instance func_unique {A : Type} `{!Unique B} : Unique (A → B).

  Global Program Instance func_unique_dep {A : Type} `{!(∀ a : A, Unique (B a))} : Unique (∀ a, B a).
End Unique.

Section JMeq.
  Lemma eq_to_jm {A} {x y : A} : x = y -> JMeq x y.
  Proof. intros ->. apply JMeq_refl. Qed.

  Lemma jm_to_eq {A} {x y : A} : JMeq x y -> x = y.
  Proof. apply JMeq_eq. Qed.

  Lemma jmeq_type_eq (A B : Type) (a : A) (b : B) : JMeq a b → A = B.
  Proof. i. depdes H. reflexivity. Qed.

  Lemma jmeq_fun_ext_dep
    A (P : A -> Type) (Q : A -> Type)
    (f : forall a, P a) (g : forall a, Q a)
    (JMEQ : forall a, JMeq (f a) (g a)) : JMeq f g.
  Proof.
    assert (P = Q) as ->.
    { apply func_ext_dep. i. eapply jmeq_type_eq, JMEQ. }
    assert (f = g) as ->; ss.
    apply func_ext_dep. i. apply jm_to_eq, JMEQ.
  Qed.

  Lemma jmeq_fun_ext A B C (f : A → B) (g : A → C)
    (JMEQ : ∀ a, JMeq (f a) (g a)) : JMeq f g.
  Proof. by eapply jmeq_fun_ext_dep. Qed.
End JMeq.