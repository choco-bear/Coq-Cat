Require Import Category CommonTactics.

Class IsIsomorphism `{C : Category Obj} {x y : Obj} (f : x ~> y) := {
  inverse_morphism : y ~> x;
  inv_morphism_left : inverse_morphism ∘ f =[C] id[x];
  inv_morphism_right : f ∘ inverse_morphism =[C] id[y]
}.
Hint Mode IsIsomorphism - - - - ! : typeclass_instances.
Global Hint Rewrite @inv_morphism_left @inv_morphism_right : normalize.

Arguments inverse_morphism {ObjC%_type_scope C%_category_scope} {x y}%_object_scope f%_morphism_scope {IsIso} : rename, simpl never.
Arguments inv_morphism_left {ObjC%_type_scope C%_category_scope} {x y}%_object_scope f%_morphism_scope {IsIso} : rename.
Arguments inv_morphism_right {ObjC%_type_scope C%_category_scope} {x y}%_object_scope f%_morphism_scope {IsIso} : rename.
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
  iso_morphism :> x ~> y;
  #[export] is_iso_morphism :: IsIsomorphism iso_morphism
}.

Declare Scope iso_scope.
Delimit Scope iso_scope with iso.
Bind Scope iso_scope with Isomorphic.

Arguments iso_morphism {Obj%_type_scope C%_category_scope} [x y]%_object_scope ! ISO%_iso_scope : rename.

Notation "x ≅ y" := (Isomorphic x%object y%object) (at level 70, no associativity) : type_scope.
Notation "x '≅[' C ']' y" := (@Isomorphic _ C%category x%object y%object)
  (at level 70, no associativity, format "x  ≅[ C ]  y") : type_scope.

Section IsomorphicEquivalence.
  Context `{C : Category Obj}.

  Definition isomorphic_refl (x : Obj) : x ≅ x := {| iso_morphism := id[x] |}.
  
  Definition isomorphic_sym {x y : Obj} (H : x ≅ y) : y ≅ x := {| iso_morphism := H⁻¹ |}.

  Definition isomorphic_trans {x y z : Obj} (H1 : x ≅ y) (H2 : y ≅ z) : x ≅ z := {| iso_morphism := H2 ∘ H1 |}.

  Global Program Instance isomorphic_is_cequivalence : CEquivalence (@Isomorphic _ C) :=
    {|
      CEquivalence_CReflexive := isomorphic_refl;
      CEquivalence_CSymmetric := @isomorphic_sym;
      CEquivalence_CTransitive := @isomorphic_trans;
    |}.
End IsomorphicEquivalence.

Notation "'id[' x ']'" := (isomorphic_refl x%object) : iso_scope.
Notation "'id'" := (isomorphic_refl _) (only parsing) : iso_scope.
Notation "H1 ∘ H2" := (isomorphic_trans H2%iso H1%iso) : iso_scope.
Notation "H '⁻¹'" := (isomorphic_sym H%iso) : iso_scope.

Section IsomorphicOpposite.
  Context `{C : Category Obj}.

  Program Instance isomorphic_opposite_append (x y : Obj) (H : x ≅ y) : x ≅[C ᵒᵖ] y :=
    {|
      iso_morphism := H⁻¹;
      is_iso_morphism := {|
        inverse_morphism := H;
        inv_morphism_left := inv_morphism_right (H⁻¹);
        inv_morphism_right := inv_morphism_left (H⁻¹)
      |}
    |}.

  Definition isomorphic_opposite_cancel (x y : Obj) (H : x ≅[C ᵒᵖ] y) : x ≅[C] y.
  Proof. depdes H. depdes is_iso_morphism0. hrepeat construct. Defined.
End IsomorphicOpposite.

Section MorphismProperty.
  Local Open Scope morphism_scope.
  Context `{C : Category Obj}.
  
  Class Idempotent `(f : x ~> x) := { idempotent : f ∘ f = f }.

  Class SplitIdempotent `(f : x ~> x) := {
    split_obj : Obj;
    split_epic : x ~> split_obj;
    split_monic : split_obj ~> x;
    split_comp_orig : split_monic ∘ split_epic = f;
    split_comp_id : split_epic ∘ split_monic = id;
  }.

  Context {x y : Obj} (f : x ~> y).

  Class Monic := {
    #[export] monic {z} :: Inj (=) (=) ((∘) f : z ~> x → _)
  }.

  Class Epic := {
    #[export] epic {z} :: Inj (=) (=) ((.∘ f) : y ~> z → _)
  }.

  Class BiMorphic := {
    #[export] bimorphic_monic :: Monic;
    #[export] bimorphic_epic  :: Epic;
  }.

  Class RetractionOf := {
    retraction    :> y ~> x;
    retr_left_inv : retraction ∘ f = id;
  }.

  Class SectionOf := {
    section        :> y ~> x;
    sect_right_inv : f ∘ section = id;
  }.
End MorphismProperty.
Global Hint Rewrite @retr_left_inv @sect_right_inv @split_comp_id : normalize.

Section MorphismPropertySimpl.
  Local Open Scope morphism_scope.
  Context `{C : Category Obj}.

  Lemma retr_simpl `(f : x ~> y) `(g : x ~> z) {r : RetractionOf f} : g ∘ r ∘ f = g.
  Proof. cby rewrite -comp_assoc retr_left_inv. Qed.

  Lemma sect_simpl `(f : x ~> y) `(g : y ~> z) {s : SectionOf f} : g ∘ f ∘ s = g.
  Proof. cby rewrite -comp_assoc sect_right_inv. Qed.

  Lemma split_idempotent_simpl1 `(f : x ~> x) `{!SplitIdempotent f} `(g : split_obj ~> y) : g ∘ split_epic ∘ split_monic = g.
  Proof. cby rewrite -comp_assoc split_comp_id. Qed.

  Lemma split_idempotent_simpl2 `(f : x ~> x) `{!SplitIdempotent f} `(g : x ~> y) : g ∘ split_monic ∘ split_epic = g ∘ f.
  Proof. cby rewrite -comp_assoc split_comp_orig. Qed.
End MorphismPropertySimpl.
Global Hint Rewrite @retr_simpl @sect_simpl @split_idempotent_simpl1 @split_idempotent_simpl2 : normalize.

Class IsGroupoid `(C : Category Obj) := {
  #[export] is_groupoid {x y} (f : x ~> y) :: IsIsomorphism f
}.

Hint Extern 10 (?y ~> ?x) =>
  match goal with
  | [ f : ?x ~> ?y |- _ ] => exact (f⁻¹)%morphism
  end : coqcat.

Class IsGroup `(G : Category Obj) := {
  #[export] group_is_monoid :: IsMonoid G;
  #[export] group_is_groupoid :: IsGroupoid G;
}.