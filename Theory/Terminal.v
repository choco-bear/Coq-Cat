Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

Class Terminal {C : Category} :=
  { terminal_obj : C 
  ; one {x} : x ~> terminal_obj
  ; one_unique {x} (f g : x ~> terminal_obj) : f ≡ g
  }.
#[export] Hint Resolve @one @one_unique : category_laws.

Notation "1" := terminal_obj : object_scope.
Notation "'Terminal[' C ']'" := (@Terminal C)
  (at level 9, format "Terminal[ C ]") : category_theory_scope.

Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≡ one.
Proof. intros; apply one_unique. Qed.

Notation "'one[' x ']'" := (@one _ _ x)
  (at level 9, format "one[ x ]") : morphism_scope.

Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].

Class IsTerminal {C : Category} (T : C) :=
  { terminal_morphism {x} : x ~> T
  ; terminal_unique {x} (f g : x ~> T) : f ≡ g
  }.

Instance Terminal_IsTerminal `{@Terminal C} : @IsTerminal C 1.
Proof. construct; cat. Qed.

Lemma terminal_iso `{@Terminal C} `{@IsTerminal C T} : T ≅ 1.
Proof.
  isomorphism; first [ apply terminal_unique
                     | apply terminal_morphism
                     ].
Qed.
Arguments terminal_iso {_%_category_scope _} _%_object_scope {_}.
#[export] Hint Rewrite @terminal_iso : normalize. 

#[export]
Instance proper_terminal {C} : Proper (@Isomorphism C ==> arrow) IsTerminal.
Proof.
  construct; try exact (X ∘ terminal_morphism).
  pose (terminal_unique (X⁻¹ ∘ f) (X⁻¹ ∘ g)).
  by comp_left X in e.
Qed.