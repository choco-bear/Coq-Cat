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
  Global Instance Functor_Setoid {C : Category} {D : Category}
    : Setoid (C ⟶ D) := @ob_setoid Fun[C,D].

  #[export]
  Instance Functor_Compose_respects
    {C : Category} {D : Category} {E : Category}
    : Proper (equiv ==> equiv ==> equiv) (@Functor_Compose C D E).
  Proof.
    intros F1 G1 η1 F2 G2 η2.
    simpl in * |-. unfold ob_equiv in * |-.
    srapply (Component_Is_Iso_NatIso {| component := λ x, _ |}).
    { exact (fmap[G1] (to η2 x) ∘ to η1 (F2 x)). } (* [to η] *)
    { (* naturality *)
      simpl; intros. rewrite <- naturality, <- comp_assoc, <- fmap_comp.
      rewrite naturality. comp_right. by rewrite <- fmap_comp, naturality.
    } simpl. construct.
    { exact (η1⁻¹ (F2 x) ∘ fmap[G1] (η2⁻¹ x)). } (* [from η] *)
    - (* to ∘ from ≡ id *)
      rewrite <- comp_assoc, (comp_assoc (to η1 _)), (iso_to_from η1 (F2 x)).
      simpl. by rewrite id_left, <- fmap_comp, (iso_to_from η2 x).
    - (* from ∘ to ≡ id *)
      rewrite <- comp_assoc, (comp_assoc (fmap[G1] _)).
      rewrite <- fmap_comp, (iso_from_to η2 x), fmap_id.
      by rewrite id_left, (iso_from_to η1 (F2 x)).
  Defined.

  Definition Functor_Compose_Id_left
    {C : Category} {D : Category} (F : C ⟶ D) : Id[D] ◯ F ≡ F.
  Proof.
    srapply (Component_Is_Iso_NatIso {| component := λ x, _ |}).
    { exact id[F x]. } { by intros. } construct; by try exact id[F x].
  Defined.

  Definition Functor_Compose_Id_right
    {C : Category} {D : Category} (F : C ⟶ D) : F ◯ Id[C] ≡ F.
  Proof.
    srapply (Component_Is_Iso_NatIso {| component := λ x, _ |}).
    { exact id[F x]. } { by intros. } construct; by try exact id[F x].
  Defined.

  Definition Functor_Compose_Assoc
    {B : Category} {C : Category} {D : Category} {E : Category}
    (F : D ⟶ E) (G : C ⟶ D) (H : B ⟶ C)
    : F ◯ (G ◯ H) ≡ (F ◯ G) ◯ H.
  Proof.
    srapply (Component_Is_Iso_NatIso {| component := λ x, _ |}).
    { exact id[F (G (H x))]. } { by intros. }
    construct; by try exact id[F (G (H x))].
  Defined.

  Definition Functor_Compose_Assoc_Sym
    {B : Category} {C : Category} {D : Category} {E : Category}
    (F : D ⟶ E) (G : C ⟶ D) (H : B ⟶ C)
    : (F ◯ G) ◯ H ≡ F ◯ (G ◯ H).
  Proof.
    srapply (Component_Is_Iso_NatIso {| component := λ x, _ |}).
    { exact id[(F ◯ G) (H x)]. } { by intros. }
    construct; by try exact id[(F ◯ G) (H x)].
  Defined.
End Functor_Setoid.