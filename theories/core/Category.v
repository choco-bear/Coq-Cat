Require Import CommonTactics.

Class Category (Obj : Type) := mk_Category {
  Arrow : Obj → Obj → Type;

  comp {x y z} : Arrow y z → Arrow x y → Arrow x z;
  comp_assoc {x y z w} (f : Arrow z w) (g : Arrow y z) (h : Arrow x y)
    : comp f (comp g h) = comp (comp f g) h;

  cat_id x : Arrow x x;
  cat_id_left {x y} (f : Arrow x y) : comp (cat_id y) f = f;
  cat_id_right {x y} (f : Arrow x y) : comp f (cat_id x) = f;
}.
Global Hint Rewrite @comp_assoc @cat_id_left @cat_id_right : normalize.

Local Definition _obj [T : Type] : Category T → Type := λ _, T.

Local Definition _dom `{Category Obj} `(Arrow x y) : Obj := x.
Local Definition _cod `{Category Obj} `(Arrow x y) : Obj := y.

Declare Scope coqcat_scope.
Declare Scope category_scope.
Declare Scope object_scope.
Declare Scope morphism_scope.

Bind Scope category_scope with Category.
Bind Scope morphism_scope with Arrow.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope morphism_scope with morphism.
Delimit Scope coqcat_scope with coacat.

#[export] Open Scope coqcat_scope.

Arguments _obj [Obj%_type_scope] C%_category_scope : rename.
Arguments Arrow {Obj%_type_scope C%_category_scope} (x y)%_object_scope : rename.
Arguments _dom {Obj%_type_scope C%_category_scope x%_object_scope y%_object_scope} f%_morphism_scope : rename.
Arguments _cod {Obj%_type_scope C%_category_scope x%_object_scope y%_object_scope} f%_morphism_scope : rename.
Arguments comp {Obj%_type_scope C%_category_scope} {x y z}%_object_scope (f g)%_morphism_scope : rename, simpl never.
Arguments cat_id {Obj%_type_scope C%_category_scope x%_object_scope} : rename, simpl never.

Notation "'obj[' C ']'" := (_obj C%category) (at level 9, no associativity, format "obj[ C ]") : type_scope.
Notation "'hom[' C ']'" := (@Arrow _ C%category) (at level 9, no associativity, format "hom[ C ]") : type_scope.
Notation "'dom' f" := (_dom f%morphism) (at level 8, right associativity) : object_scope.
Notation "'cod' f" := (_cod f%morphism) (at level 8, right associativity) : object_scope.

Notation "x '~>' y" := (Arrow x%object y%object) (at level 90, right associativity) : type_scope.
Notation "x '~{' C '}~>' y" := (@Arrow _ C%category x%object y%object) (at level 90, only parsing) : type_scope.
Notation "x '<~' y" := (y ~> x) (at level 90, only parsing) : type_scope.
Notation "x '<~{' C '}~' y" := (y ~{C}~> x) (at level 90, only parsing) : type_scope.

Notation "'id'" := cat_id (at level 0, only parsing) : morphism_scope.
Notation "'id[' x ']'" := (@cat_id _ _ x%object) (at level 9, no associativity, format "id[ x ]") : morphism_scope.
Notation "'id{' C '}'" := (@cat_id _ C%category _) (at level 9, no associativity, only parsing) : morphism_scope.
Notation "'id{' C '}[' x ']'" := (@cat_id _ C%category x%object) (at level 9, no associativity, only parsing) : morphism_scope.

Notation "f ∘ g" := (comp f%morphism g%morphism) : morphism_scope.
Notation "f '∘[' C ']' g" := (@comp _ C%category _ _ _ f%morphism g%morphism) (at level 40, only parsing) : morphism_scope.

Notation "f '=[' C ']' g" := (f%morphism = g%morphism :> (hom[C%category] _ _))
  (at level 60, no associativity, only parsing) : coqcat_scope.

Lemma cat_ext_JMeq `(C : Category Obj) `(C' : Category Obj')
  : Obj = Obj'
  → JMeq hom[C] hom[C']
  → JMeq (@comp _ C) (@comp _ C')
  → JMeq (@cat_id _ C) (@cat_id _ C')
  → JMeq C C'.
Proof.
  rewrite /Category.comp /Category.cat_id.
  intros <- eqHom eqComp eqId. depdes C C'. ss.
  apply JMeq_eq in eqHom as ->.
  apply JMeq_eq in eqComp as ->.
  apply JMeq_eq in eqId as ->.
  replace comp_assoc0 with comp_assoc1 by apply proof_irr.
  replace cat_id_left0 with cat_id_left1 by apply proof_irr.
  by replace cat_id_right0 with cat_id_right1 by apply proof_irr.
Qed.

Lemma cat_ext [Obj : Type] (C C' : Category Obj)
  : JMeq hom[C] hom[C']
  → JMeq (@comp _ C) (@comp _ C')
  → JMeq (@cat_id _ C) (@cat_id _ C')
  → C = C'.
Proof. by i; apply JMeq_eq, cat_ext_JMeq. Qed.

Program Definition Opposite `(C : Category Obj) : Category Obj :=
  {|
    Arrow := λ x y, Arrow y x;
    comp := λ x y z f g, comp g f;
    cat_id := λ x, @cat_id Obj C x;
  |}.

Notation "C 'ᵒᵖ'" := (Opposite C%category) (at level 7, left associativity, format "C ᵒᵖ") : category_scope.
Notation "'(ᵒᵖ)'" := (@Opposite _) (only parsing) : coqcat_scope.
Notation "'(ᵒᵖ)@{' Obj '}'" := (@Opposite Obj%type) (at level 9, no associativity, only parsing) : coqcat_scope.

Global Instance opposite_involutive [Obj : Type] : Involutive eq (ᵒᵖ)@{Obj}.
Proof. by ii; apply cat_ext. Qed.

Program Definition BinaryProduct `(C : Category ObjC) `(D : Category ObjD) : Category (ObjC * ObjD) :=
  {|
    Arrow := λ x y, (x.1 ~{C}~> y.1) * (x.2 ~{D}~> y.2);
    comp := λ x y z f g, (f.1 ∘ g.1, f.2 ∘ g.2);
    cat_id := λ x, (id[x.1], id[x.2]);
  |}%type%morphism.

Infix "*" := BinaryProduct : category_scope.
Notation "(*)" := BinaryProduct (only parsing) : coqcat_scope.
Notation "( C *.)" := (BinaryProduct C%category) (only parsing) : coqcat_scope.
Notation "(*. D *)" := (λ C, BinaryProduct C D%category) (only parsing) : coqcat_scope.