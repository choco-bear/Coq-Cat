Require Import CommonTactics.

Class Bijective [A B : Type] (f : A → B) :=
  {
    inverse_function : B → A;
    bijective_inv_left : inverse_function ∘ f = Datatypes.id;
    bijective_inv_right : f ∘ inverse_function = Datatypes.id;
  }. 
Arguments inverse_function [A B]%_type_scope f%_function_scope {BIJECTIVE} _ : rename, simpl never.
  
Notation "f '⁻¹'" := (inverse_function f) (at level 7, left associativity, format "f ⁻¹") : function_scope.

Lemma inv_left_pointwise [A B : Type] (f : A → B) `{!Bijective f} x : f⁻¹ (f x) = x.
Proof. transitivity ((f⁻¹ ∘ f) x)=> //. rewrite bijective_inv_left=> //. Qed.

Lemma inv_right_pointwise [A B : Type] (f : A → B) `{!Bijective f} x : f (f⁻¹ x) = x.
Proof. transitivity ((f ∘ f⁻¹) x)=> //. rewrite bijective_inv_right=> //. Qed.

Lemma inv_spec [A B : Type] (f : A → B) `{!Bijective f} x y : y = f x → f⁻¹ y = x.
Proof. intros ->. apply inv_left_pointwise. Qed.

Global Hint Rewrite @bijective_inv_left @bijective_inv_right @inv_left_pointwise @inv_right_pointwise @inv_spec : normalize.

Lemma inv_normalize_1 [A B C : Type] (f : A → B) `{!Bijective f} (g : B → C) : g ∘ f ∘ f⁻¹ = g.
Proof. extensionalities=> /=. common_normalize=> //. Qed.

Lemma inv_normalize_2 [A B C : Type] (f : A → B) `{!Bijective f} (g : A → C) : g ∘ f⁻¹ ∘ f = g.
Proof. extensionalities=> /=. common_normalize=> //. Qed.

Global Hint Rewrite @inv_normalize_1 @inv_normalize_2 : normalize.

Global Instance prop_pi (P : Prop) : ProofIrrel P.
Proof. ii. apply proof_irr. Qed.

Class Unique (A : Type) := {
  #[export] unique_inhabited :: Inhabited A;
  #[export] unique_proof_irrel :: ProofIrrel A;
}.