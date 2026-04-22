Require ClassicalFacts.
Require FunctionalExtensionality.
Require ChoiceFacts.
Require IndefiniteDescription.
Require PropExtensionality.

Lemma func_ext_dep {A} {B : A -> Type} (f g : forall x, B x) : (forall x, f x = g x) -> f = g.
Proof. apply @FunctionalExtensionality.functional_extensionality_dep. Qed.

Lemma func_ext {A B} (f g : A -> B) : (forall x, f x = g x) -> f = g.
Proof. apply func_ext_dep. Qed.

Lemma dependent_functional_choice {A : Type} (B : A -> Type) :
  forall R : forall x : A, B x -> Prop,
    (forall x : A, exists y : B x, R x y) ->
    (exists f : (forall x : A, B x), forall x : A, R x (f x)).
Proof.
  eapply ChoiceFacts.non_dep_dep_functional_choice.
  clear. exact Stdlib.Logic.IndefiniteDescription.functional_choice.
Qed.

Lemma prop_ext (P Q : Prop) : (P <-> Q) -> P = Q.
Proof. apply PropExtensionality.propositional_extensionality. Qed.

Lemma pred_ext {A} (P Q : A -> Prop) : (forall x : A, P x <-> Q x) -> P = Q.
Proof. intros. apply func_ext. intros. apply prop_ext. auto. Qed.

Lemma proof_irr [P : Prop] (p q : P) : p = q.
Proof.
  cut (P = True).
  { intros ->. destruct p, q. reflexivity. }
  apply prop_ext. intuition.
Qed.