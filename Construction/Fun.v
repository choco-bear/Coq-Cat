Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.
Require Import Category.Theory.Isomorphism.

Generalizable All Variables.

(** Being given two categories [C] and [D], functors from [C] to [D] form a
  * category, whose objects are functors, and whose morphisms are natural
  * transformations.
  *)
Program Definition Fun@{o1 o2 h o p u1 u2}
  (C : Category@{o1 h h}) (D : Category@{o2 h h}) : Category@{o p p} :=
    {| obj := C ⟶ D
    ; hom := λ F G, F ⟹ G
    ; homset := λ F G, NaturalTransform_Setoid@{o1 h u2 o2 h h p u1}
    ; id := @NaturalTransform_id _ _
    ; compose := @NaturalTransform_compose _ _

    ; compose_respects := @NaturalTransform_compose_respects _ _

    ; id_left := λ F G η x, id_left (η x)
    ; id_right := λ F G η x, id_right (η x)

    ; comp_assoc := λ F G H K η μ ν x,
        comp_assoc (η x) (μ x) (ν x)
    ; comp_assoc_sym := λ F G H K η μ ν x,
        comp_assoc_sym (η x) (μ x) (ν x)
    |}.

Notation "Fun[ C , D ]" := (Fun C%category D%category)
  (at level 0, format "Fun[ C , D ]") : category_scope.

(** If every component of a natural transformation is an isomorphism, then the
  * natural transformation itself is an isomorphism in the functor category. We
  * call such natural transformations "natural isomorphisms".
  *)
Program Definition Component_Is_Iso_NatIso
  {C : Category} {D : Category} {F G : C ⟶ D}
  (η : F ⟹ G) (H : ∀ x : C, IsIsomorphism (η x)) : F ≅[Fun[C,D]] G :=
  {| to := η
   ; from := {| component := λ x, from (IsIsoToIso _ (H x)) |}
   ; iso_to_from := _
   ; iso_from_to := _
  |}.
Next Obligation.
  spose (naturality η f) as EQ.
  comp_left two_sided_inverse in EQ.
  comp_right two_sided_inverse in EQ.
  rewrite !comp_assoc, is_left_inverse, id_left in EQ.
  by rewrite <- !comp_assoc, is_right_inverse, id_right in EQ.
Qed.
Next Obligation. by rewrite is_right_inverse. Qed.
Next Obligation. by rewrite is_left_inverse. Qed.

(** Conversely, if a natural transformation is an isomorphism in the functor
  * category, then each of its components is an isomorphism in the target
  * category.
  *)
Program Definition NatIso_Component_Iso
  {C : Category} {D : Category} {F G : C ⟶ D}
  (η : F ≅[Fun[C,D]] G) (x : C) : F x ≅ G x :=
    {| to := to η x
     ; from := from η x
     ; iso_to_from := iso_to_from η x
     ; iso_from_to := iso_from_to η x
    |}.