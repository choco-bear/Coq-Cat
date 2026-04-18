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
