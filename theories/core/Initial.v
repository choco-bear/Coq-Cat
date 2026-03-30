Require Import CommonTactics CommonFacts Category Morphism.

Class IsInitial `[C : Category Obj] (I : Obj) := {
  #[export] is_initial_unique c :: Unique (I ~> c)
}.

Notation "'IsInitial@[' C ']'" := (@IsInitial _ C%category)
  (at level 9, no associativity, format "IsInitial@[ C ]") : coqcat_scope.
Notation "'IsTerminal@[' C ']'" := (@IsInitial _ (C%category ᵒᵖ))
  (at level 9, no associativity, format "IsTerminal@[ C ]") : coqcat_scope.

Section Facts.
  Context `{C : Category Obj}.

  Definition initials_are_isomorphic (I I' : Obj) `{!IsInitial@[C] I} `{!IsInitial@[C] I'} : Isomorphic I I'.
  Proof. hrepeat construct; common_simpl. Defined.

  Definition terminals_are_isomorphic (T T' : Obj) `{!IsTerminal@[C] T} `{!IsTerminal@[C] T'} : Isomorphic T T'.
  Proof. hrepeat construct; repeat_on_hyps (fun H => apply H). Defined.
End Facts.
#[export] Hint Resolve @initials_are_isomorphic @terminals_are_isomorphic : coqcat.

Goal ∀ (Obj : Type) (C : Category Obj) (T T' : Obj) (TERMINAL : IsTerminal@[C] T) (TERMINAL' : IsTerminal@[C] T'), T ≅[C] T'.
Proof. common_simpl. Qed.