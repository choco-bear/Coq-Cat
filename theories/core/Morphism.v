Require Import Category CommonTactics.

Class IsIsomorphism `{C : Category Obj} {x y : Obj} (f : x ~> y) := {
  inverse_morphism : y ~> x;
  inv_morphism_left : inverse_morphism ∘ f =[C] id[x];
  inv_morphism_right : f ∘ inverse_morphism =[C] id[y]
}.
Global Hint Rewrite @inv_morphism_left @inv_morphism_right : normalize.

Arguments inverse_morphism {ObjC%_type_scope C%_category_scope} {x y}%_object_scope f%_morphism_scope {IsIso} : rename, simpl never.
Notation "f '⁻¹'" := (inverse_morphism f%morphism) (at level 7, left associativity, format "f ⁻¹") : morphism_scope.

Section InverseNorm.
  Context `{C : Category Obj}.
  Context {x y : Obj} (f : x ~> y) `{!IsIsomorphism f}.

  Lemma morphism_inv_norm_1 {z : Obj} (g : y ~> z) : g ∘ f ∘ f⁻¹ =[C] g.
  Proof. rewrite -comp_assoc inv_morphism_right; common_simpl. Qed.

  Lemma morphism_inv_norm_2 {z : Obj} (g : x ~> z) : g ∘ f⁻¹ ∘ f =[C] g.
  Proof. rewrite -comp_assoc inv_morphism_left; common_simpl. Qed.
End InverseNorm.
Global Hint Rewrite @morphism_inv_norm_1 @morphism_inv_norm_2 : normalize.

Section IsomorphismInstances.
  Context `{C : Category Obj}.

  Global Program Instance id_is_iso (x : Obj) : IsIsomorphism id[x] := {| inverse_morphism := id[x] |}.

  Global Program Instance inv_is_iso {x y : Obj} (f : x ~> y) `{!IsIsomorphism f}
    : IsIsomorphism (f⁻¹) | 10 := {| inverse_morphism := f |}.

  Global Program Instance iso_comp_is_iso {x y z : Obj} (f : y ~> z) `{!IsIsomorphism f} (g : x ~> y) `{!IsIsomorphism g}
    : IsIsomorphism (f ∘ g) | 30 := {| inverse_morphism := g⁻¹ ∘ f⁻¹ |}.

  Lemma inv_involutive {x y : Obj} (f : x ~> y) `{!IsIsomorphism f} : (f⁻¹)⁻¹ =[C] f.
  Proof. ss. Qed.

  Lemma comp_inv {x y z : Obj} (f : y ~> z) `{!IsIsomorphism f} (g : x ~> y) `{!IsIsomorphism g} : (f ∘ g)⁻¹ =[C] g⁻¹ ∘ f⁻¹.
  Proof. ss. Qed.

  Lemma id_inv_id {x : Obj} : id[x]⁻¹ =[C] id.
  Proof. ss. Qed.
End IsomorphismInstances.
Global Hint Rewrite @inv_involutive @comp_inv @id_inv_id : normalize.

Class Isomorphic `{C : Category Obj} (x y : Obj) := {
  #[export] iso_morphism :> x ~> y;
  #[export] is_iso_morphism :: IsIsomorphism iso_morphism
}.

Declare Scope iso_scope.
Delimit Scope iso_scope with iso.
Bind Scope iso_scope with Isomorphic.

Notation "x ≅ y" := (Isomorphic x%object y%object) (at level 70, no associativity) : iso_scope.
Notation "x '≅[' C ']' y" := (@Isomorphic _ C%category x%object y%object)
  (at level 70, no associativity, format "x  ≅[ C ]  y") : iso_scope.

Section IsomorphicEquivalence.
  Context `{C : Category Obj}.
  Local Open Scope iso_scope.

  Definition isomorphic_refl (x : Obj) : (x ≅ x) := {| iso_morphism := id[x] |}.
  
  Definition isomorphic_sym {x y : Obj} (H : x ≅ y) : y ≅ x := {| iso_morphism := (iso_morphism)⁻¹ |}.

  Definition isomorphic_trans {x y z : Obj} (H1 : x ≅ y) (H2 : y ≅ z) : x ≅ z :=
    {| iso_morphism := @iso_morphism _ _ y z H2 ∘ @iso_morphism _ _ x y H1 |}.

  Global Program Instance isomorphic_is_cequivalence : CEquivalence (@Isomorphic _ C) :=
    {|
      CEquivalence_CReflexive := isomorphic_refl;
      CEquivalence_CSymmetric := @isomorphic_sym;
      CEquivalence_CTransitive := @isomorphic_trans;
    |}.
End IsomorphicEquivalence.

Notation "H1 ∘ H2" := (isomorphic_trans H1%iso H2%iso) : iso_scope.
Notation "H '⁻¹'" := (isomorphic_sym H%iso) : iso_scope.