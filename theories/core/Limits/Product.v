Require Import CommonTactics CommonFacts Category Morphism.

Class IsProduct `[C : Category Obj] [I : Type] (F : I → Obj) (P : Obj) (pi : ∀ i, P ~> F i) := {
  product_morphism [X] (f : ∀ i, X ~> F i) : X ~> P;
  product_morphism_commute [X] (f : ∀ i, X ~> F i) : ∀ i, f i =[C] pi i ∘ product_morphism f;
  product_morphism_unique [X] (f : ∀ i, X ~> F i) (h : X ~> P) (COMMUTE : ∀ i, f i =[C] pi i ∘ h) : h = product_morphism f;
}.

Notation "'IsProduct@[' C ']'" := (@IsProduct _ C%category _)
  (at level 9, no associativity, format "IsProduct@[ C ]") : coqcat_scope.
Notation "'IsCoproduct@[' C ']'" := (@IsProduct _ (C ᵒᵖ)%category _)
  (at level 9, no associativity, format "IsCoproduct@[ C ]") : coqcat_scope.