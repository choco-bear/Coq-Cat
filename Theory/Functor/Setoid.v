Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Fun.

(** This file defines the setoid structure for functors, and proves respectful
  * properties of functor composition.
  *)

Section Functor_Setoid.
  #[export]
  Program Instance Functor_Setoid
    {C : Category} {D : Category} : Setoid (C ⟶ D) :=
    { equiv := λ F G, { iso : ∀ x : C, F x ≅ G x
                      & ∀ (x y : C) (f : x ~> y), fmap[F] f ≡ from (iso y) ∘ fmap[G] f ∘ to (iso x)
                      }
    ; setoid_equiv := Build_Equivalence _ _ _ _
    }.
  Next Obligation.
    intros F G [ISO EQ]; construct.
    - isomorphism.
      + exact (from (ISO x)).
      + exact (to (ISO x)).
      + cat.
      + cat.
    - ss. now rewrite EQ; normalize.
  Defined.
  Next Obligation.
    intros F G H [ISO0 EQ0] [ISO1 EQ1]; construct.
    - isomorphism.
      + exact (to (ISO1 x) ∘ to (ISO0 x)).
      + exact (from (ISO0 x) ∘ from (ISO1 x)).
      + now normalize.
      + now normalize.
    - ss. now rewrite EQ0, EQ1; normalize.
  Defined.

  #[export]
  Instance Functor_Compose_respects
    {C : Category} {D : Category} {E : Category}
    : Proper (equiv ==> equiv ==> equiv) (@Functor_Compose C D E).
  Proof.
    intros F1 G1 [ISO1 EQ1] F2 G2 [ISO2 EQ2]; construct.
    - isomorphism.
      + exact (to (ISO1 _) ∘ (fmap[F1] (to (ISO2 x)))).
      + exact (from (ISO1 _) ∘ fmap[G1] (from (ISO2 x))).
      + rewrite EQ1. by normalize.
      + rewrite EQ1. now normalize.
    - ss. now rewrite !EQ1, !EQ2; normalize.
  Defined.

  Definition Functor_Compose_Id_left
    {C : Category} {D : Category} (F : C ⟶ D) : Id[D] ◯ F ≡ F.
  Proof. by construct; [exact iso_id|]. Defined.

  Definition Functor_Compose_Id_right
    {C : Category} {D : Category} (F : C ⟶ D) : F ◯ Id[C] ≡ F.
  Proof. by construct; [exact iso_id|]. Defined.

  Definition Functor_Compose_Assoc
    {B : Category} {C : Category} {D : Category} {E : Category}
    (F : D ⟶ E) (G : C ⟶ D) (H : B ⟶ C)
    : F ◯ (G ◯ H) ≡ (F ◯ G) ◯ H.
  Proof. by construct. Defined.

  Definition Functor_Compose_Assoc_Sym
    {B : Category} {C : Category} {D : Category} {E : Category}
    (F : D ⟶ E) (G : C ⟶ D) (H : B ⟶ C)
    : (F ◯ G) ◯ H ≡ F ◯ (G ◯ H).
  Proof. by construct. Defined.
End Functor_Setoid.