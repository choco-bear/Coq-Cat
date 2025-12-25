Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Ltac reassociate_right := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_left := repeat (rewrite comp_assoc); cat.

Section Morphisms.
  Context {C : Category}.

  (** A morphism is an epimorphism if it is right-cancellable. *)
  Class Epic {x y} (f : x ~> y) := 
    { epic : ∀ z (g1 g2 : y ~> z), g1 ∘ f ≡ g2 ∘ f → g1 ≡ g2 }.

  (** A morphism is a monomorphism if it is left-cancellable. *)
  Class Monic {x y} (f : x ~> y) := 
    { monic : ∀ z (g1 g2 : z ~> x), f ∘ g1 ≡ f ∘ g2 → g1 ≡ g2 }.

  (** A morphism is a bimorphism if it is both an epimorphism and a monomorphism. *)
  Definition BiMorphic {x y} (f : x ~> y) := Epic f * Monic f.

  (** Lemmas about identity morphisms *)
  Section Id.
    Corollary id_epic {x : C} : Epic id[x].
    Proof. construct. now rewrite !id_right in X. Qed.

    Corollary id_monic {x : C} : Monic id[x].
    Proof. construct. now rewrite !id_left in X. Qed.

    Corollary id_bimorphic {x : C} : BiMorphic id[x].
    Proof. split; [apply id_epic|apply id_monic]. Qed.
  End Id.

  (** Lemmas about inverse morphisms *)
  Section Inverse.
    Context {x y : C} {f : x ~> y}.

    Lemma has_right_inverse_epic
      : (∃ g, f ∘ g ≡ id) → Epic f.
    Proof.
      intros [g EQ]. construct.
      rewrite <- id_right, <- (id_right g2).
      rewrite <- EQ. reassociate_left.
    Qed.

    Lemma has_left_inverse_monic
      : (∃ g, g ∘ f ≡ id) → Monic f.
    Proof.
      intros [g EQ]. construct.
      rewrite <- id_left, <- (id_left g2).
      rewrite <- EQ. reassociate_right.
    Qed.
  End Inverse.

  (** Lemmas about composition of morphisms *)
  Section Composition.
    Context {x y z : C} {f : y ~> z} {g : x ~> y}.

    Definition epi_compose  :
      Epic f → Epic g → Epic (f ∘ g).
    Proof.
      construct. do 2 apply epic.
      reassociate_right.
    Qed.

    Definition monic_compose :
      Monic f → Monic g → Monic (f ∘ g).
    Proof.
      construct. do 2 apply monic.
      reassociate_left.
    Qed.
  End Composition.
End Morphisms.
#[export] Hint Unfold BiMorphic : core.