Require Import CommonTactics CommonFacts Category Morphism.

Class IsInitial `[C : Category Obj] (I : Obj) := {
  #[export] is_initial_unique c :: Unique (I ~> c)
}.

Notation "'IsInitial@[' C ']'" := (@IsInitial _ C%category)
  (at level 9, no associativity, format "IsInitial@[ C ]") : coqcat_scope.
Notation "'IsTerminal@[' C ']'" := (@IsInitial _ (C ᵒᵖ)%category)
  (at level 9, no associativity, format "IsTerminal@[ C ]") : coqcat_scope.

#[export]
Instance is_terminal_unique `{C : Category Obj} `{!IsTerminal@[C] T} c : Unique (c ~> T) := @is_initial_unique _ (C ᵒᵖ) _ _ c.

Section Facts.
  Context `{C : Category Obj}.

  Definition initials_are_isomorphic (I I' : Obj) `{!IsInitial@[C] I} `{!IsInitial@[C] I'} : Isomorphic I I'.
  Proof. hrepeat construct; common_simpl. Defined.

  Definition terminals_are_isomorphic (T T' : Obj) `{!IsTerminal@[C] T} `{!IsTerminal@[C] T'} : Isomorphic T T'.
  Proof. hrepeat construct; repeat_on_hyps (fun H => apply H). Defined.
End Facts.
#[export] Hint Resolve @initials_are_isomorphic @terminals_are_isomorphic : coqcat.

Class HasNullObject `(C : Category Obj) := {
  null_object : Obj;
  #[export] null_object_is_initial :: IsInitial@[C] null_object;
  #[export] null_object_is_terminal :: IsTerminal@[C] null_object;
}.

Definition zero_morphism `{C : Category Obj} `{!HasNullObject C} x y : x ~> y := ((● : null_object ~> y) ∘ ●)%morphism.

Notation "0" := null_object (only parsing) : object_scope.
Notation "'0[' C ']'" := (@null_object _ C%category _) (format "0[ C ]") : object_scope.
Notation "0" := (zero_morphism _ _) (only parsing) : morphism_scope.
Notation "'0⟨' a ',' b '⟩'" := (zero_morphism a%object b%object) (format "0⟨ a ,  b ⟩") : morphism_scope.

Section ZeroSimpl.
  Local Open Scope morphism_scope.
  Context `{C : Category Obj} `{!HasNullObject C}.

  Lemma zero_left_comp_zero {x y z: Obj} (f : x ~> y) : 0⟨y,z⟩ ∘ f = 0.
  Proof. cby rewrite -comp_assoc; cut (● ∘ f = ●); try intros ->. Qed.

  Lemma zero_right_comp_zero {x y z : Obj} (f : y ~> z) : f ∘ 0⟨x,y⟩ = 0.
  Proof. cby rewrite comp_assoc; cut (f ∘ ● = ●); try intros ->. Qed.
End ZeroSimpl.
#[export] Hint Rewrite @zero_left_comp_zero @zero_right_comp_zero : normalize.