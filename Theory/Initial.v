Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Terminal.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(* To be initial is just to be terminal in the opposite category; but to avoid
   confusion, we want a set of notations specific to categories with initial
   objects. *)

Notation "'Initial[' C ']'" := (@Terminal (C^op))
  (at level 9, format "Initial[ C ]") : category_theory_scope.
Notation "@Initial C" := (@Terminal (C^op))
  (at level 9, only parsing) : category_theory_scope.

Section Initial_.
  Context `{I : @Initial C}.

  Definition initial_obj : C := @terminal_obj _ I.
  Definition zero {x} : initial_obj ~{C}~> x := @one _ I _.

  Definition zero_unique {x} (f g : initial_obj ~{C}~> x) : f ≡ g :=
    @one_unique _ I _ _ _.
End Initial_.
#[export] Hint Resolve @zero @zero_unique : category_laws.

Notation "0" := initial_obj : object_scope.

Notation "zero[ C ]" := (@zero _ _ C)
  (at level 9, format "zero[ C ]") : morphism_scope.

Corollary zero_comp `{T : @Initial C} {x y : C} {f : x ~> y} :
  f ∘ zero ≡ zero.
Proof. apply (@one_comp _ T). Qed.

Class IsInitial {C : Category} (I : C) :=
  { initial_morphism {x} : I ~> x
  ; initial_unique {x} (f g : I ~> x) : f ≡ g
  }.

Instance Initial_IsInitial `{@Initial C} : @IsInitial C 0.
Proof. construct; cat. Qed.

Lemma initial_iso `{@Initial C} `{@IsInitial C T} : T ≅ 0.
Proof.
  isomorphism; first [ apply initial_unique
                     | apply initial_morphism
                     ].
Qed.
Arguments initial_iso {_%_category_scope _} _%_object_scope {_}.
#[export] Hint Rewrite @initial_iso : normalize. 

#[export]
Instance proper_initial {C} : Proper (@Isomorphism C ==> arrow) IsInitial.
Proof.
  construct; try exact (initial_morphism ∘ X⁻¹).
  pose (initial_unique (f ∘ X) (g ∘ X)).
  by comp_right (X⁻¹) in e.
Qed.