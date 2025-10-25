Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Section Morphisms.
  Context {C : Category}.
  Open Scope type_scope.

  (** A morphism is an epimorphism if it is right-cancellable. *)
  Class Epic {x y} (f : x ~> y) := 
    { epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≡ g2 ∘ f → g1 ≡ g2 }.

  (** A morphism is a monomorphism if it is left-cancellable. *)
  Class Monic {x y} (f : x ~> y) := 
    { monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≡ f ∘ g2 → g1 ≡ g2 }.
End Morphisms.