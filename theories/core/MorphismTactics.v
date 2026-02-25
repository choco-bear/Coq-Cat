Require Import CommonTactics CommonFacts.
Require Import Category CategoryTactics CategoryFacts.
Require Import Functor FunctorTactics FunctorFacts.
Require Import Morphism.

Local Open Scope morphism_scope.

Lemma left_cancel `{C : Category Obj} [x y z : Obj] (f g : x ~> y) (h : y ~> z) `{!IsIsomorphism h}
  : h ∘ f =[C] h ∘ g → f = g.
Proof. i. comp_l h⁻¹ in H. common_simpl. Qed.

Lemma right_cancel `{C : Category Obj} [x y z : Obj] (f g : y ~> z) (h : x ~> y) `{!IsIsomorphism h}
  : f ∘ h =[C] g ∘ h → f = g.
Proof. i. comp_r h⁻¹ in H. common_simpl. Qed.

Tactic Notation "comp_l" uconstr(p) :=
  autorewrite with assoc_right; unshelve simple refine (left_cancel _ _ p _); autorewrite with assoc_left.

Tactic Notation "comp_r" uconstr(p) :=
  autorewrite with assoc_left; unshelve simple refine (right_cancel _ _ p _); autorewrite with assoc_left.