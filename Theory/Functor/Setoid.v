Require Import Category.Lib.
Require Import Category.Theory.Category.
From Category.Theory Require Export Functor Natural Isomorphism.
Require Export Category.Construction.Fun.

Generalizable Variables All.

Ltac functor_equiv_solver := construct; unshelve by first [natural_transform|ss].

(** Setoid Structure for functors. *)
Section Functor_Setoid.
  #[export]
  Program Instance Functor_Setoid
    {C : Category} {D : Category} : Setoid (C ⟶ D) :=
    { (** The pointwise object equality makes the proofs too tedious since
        * [fmap[F] f] and [fmap[G] f] have different types in the type system of
        * Rocq. Of course, we can transport them along equalities, but that makes
        * the proofs quite verbose. Instead, we use natural isomorphisms between
        * [F] and [G], which is more flexible and convenient.
        *)
      equiv := @Isomorphism Fun[C,D]
    ; setoid_equiv := @iso_equivalence Fun[C,D]
    }.

  #[export]
  Instance iso_of {C : Category} {D : Category} {F G : C ⟶ D} (E : F ≡ G)
    : F ≅[Fun[C,D]] G := E.

  #[export]
  Instance Functor_Compose_respects
    {C : Category} {D : Category} {E : Category}
    : Proper (equiv ==> equiv ==> equiv) (@Functor_Compose C D E).
  Proof.
    proper; construct.
    - exact (to X ▪ to X0).
    - exact (from X ▪ from X0).
    - rewrite <-interchange_law, !iso_to_from. by ss.
    - rewrite <-interchange_law, !iso_from_to. by ss.
  Qed.

  Definition Functor_Compose_Id_left
    {C : Category} {D : Category} (F : C ⟶ D) : Id[D] ◯ F ≡ F.
  Proof. by functor_equiv_solver. Defined.

  Definition Functor_Compose_Id_right
    {C : Category} {D : Category} (F : C ⟶ D) : F ◯ Id[C] ≡ F.
  Proof. by functor_equiv_solver. Defined.

  Definition Functor_Compose_Assoc
    {B : Category} {C : Category} {D : Category} {E : Category}
    (F : D ⟶ E) (G : C ⟶ D) (H : B ⟶ C)
    : F ◯ (G ◯ H) ≡ (F ◯ G) ◯ H.
  Proof. by functor_equiv_solver. Defined.

  Definition Functor_Compose_Assoc_Sym
    {B : Category} {C : Category} {D : Category} {E : Category}
    (F : D ⟶ E) (G : C ⟶ D) (H : B ⟶ C)
    : (F ◯ G) ◯ H ≡ F ◯ (G ◯ H).
  Proof. by functor_equiv_solver. Defined.

  Lemma nat_iso_to_from {C : Category} {D : Category} {F G : C ⟶ D} (I : F ≡ G) x
    : to I x ∘ from I x ≡ id.
  Proof. now transitivity ((I ∘ I⁻¹) x); try by rewrite (iso_to_from I x). Qed.

  Lemma nat_iso_from_to {C : Category} {D : Category} {F G : C ⟶ D} (I : F ≡ G) x
    : from I x ∘ to I x ≡ id.
  Proof. now transitivity ((I⁻¹ ∘ I) x); try by rewrite (iso_from_to I x). Qed.

  Lemma nat_iso_simpl_1
    {C : Category} {D : Category} {F G : C ⟶ D} (I : F ≡ G) x {y} (f : G x ~> y)
    : f ∘ to I x ∘ from I x ≡ f.
  Proof. by rewrite <-comp_assoc, nat_iso_to_from. Qed.

  Lemma nat_iso_simpl_2
    {C : Category} {D : Category} {F G : C ⟶ D} (I : F ≡ G) x {y} (f : F x ~> y)
    : f ∘ from I x ∘ to I x ≡ f.
  Proof. by rewrite <-comp_assoc, nat_iso_from_to. Qed.
End Functor_Setoid.
#[export] Hint Rewrite @nat_iso_to_from @nat_iso_from_to @nat_iso_simpl_1 @nat_iso_simpl_2
                       @Functor_Compose_Id_left @Functor_Compose_Id_right
                       @Functor_Compose_Assoc : categories normalize.