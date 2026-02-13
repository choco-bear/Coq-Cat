Require Import Program Axioms sflib.
From stdpp Require Import ssreflect.

Class Category (Obj : Type) := mk_Category {
  Arrow : Obj → Obj → Type;
  
  #[export] Arrow_equiv x y :: Equiv (Arrow x y);
  #[export] Arrow_equivalence x y :: Equivalence (≡@{Arrow x y});

  comp {x y z} : Arrow y z → Arrow x y → Arrow x z;
  #[export] comp_proper {x y z} :: Proper ((≡) ==> (≡) ==> (≡)) (@comp x y z);
  comp_assoc {x y z w} (f : Arrow z w) (g : Arrow y z) (h : Arrow x y)
    : comp (comp f g) h ≡ comp f (comp g h);

  cat_id x : Arrow x x;
  cat_id_left {x y} (f : Arrow x y) : comp (cat_id y) f ≡ f;
  cat_id_right {x y} (f : Arrow x y) : comp f (cat_id x) ≡ f;
}.

Local Definition _obj [T : Type] : Category T → Type := λ _, T.
Coercion _obj : Category >-> Sortclass.

Local Definition _dom `{!Category Obj} `(Arrow x y) : Obj := x.
Local Definition _cod `{!Category Obj} `(Arrow x y) : Obj := y.

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
Arguments cat_id {Obj%_type_scope C%_category_scope x%_object_scope} : rename, simpl never.
Arguments comp {Obj%_type_scope C%_category_scope} {x y z}%_object_scope (f g)%_morphism_scope : rename, simpl never.

Notation "'obj[' C ']'" := (_obj C%category) (at level 7, only parsing) : type_scope.
Notation "'hom[' C ']'" := (@Arrow _ C%category) (at level 7, only parsing) : type_scope.
Notation "'dom' f" := (_dom f%morphism) (at level 8, right associativity) : object_scope.
Notation "'cod' f" := (_cod f%morphism) (at level 8, right associativity) : object_scope.

Notation "x '~>' y" := (Arrow x%object y%object) (at level 90, right associativity) : type_scope.
Notation "x '~{' C '}~>' y" := (@Arrow _ C%category x%object y%object) (at level 90, only parsing) : type_scope.
Notation "x '<~' y" := (y ~> x) (at level 90, only parsing) : type_scope.
Notation "x '<~{' C '}~' y" := (y ~{C}~> x) (at level 90, only parsing) : type_scope.

Notation "'id'" := cat_id (at level 0, only parsing) : morphism_scope.
Notation "'id[' x ']'" := (@cat_id _ _ x%object) (at level 7, format "id[ x ]") : morphism_scope.
Notation "'id{' C '}'" := (@cat_id _ C%category _) (at level 7, only parsing) : morphism_scope.
Notation "'id{' C '}[' x ']'" := (@cat_id _ C%category x%object) (at level 7, only parsing) : morphism_scope.

Notation "f ∘ g" := (comp f%morphism g%morphism) : morphism_scope.
Notation "f '∘[' C ']' g" := (@comp _ C%category _ _ _ f%object g%object) (at level 40, only parsing) : morphism_scope.

Notation "f '≡[' C ']' g" := (f%morphism ≡[hom[C%category] _ _] g%morphism)
  (at level 70, no associativity, only parsing) : coqcat_scope.

Definition Opposite [Obj : Type] (C : Category Obj) : Category Obj :=
  {|
    Arrow := λ x y, Arrow y x;
    Arrow_equiv := λ x y, Arrow_equiv y x;

    comp := λ x y z f g, comp g f;
    comp_proper := λ x y z f1 f2 feq g1 g2 geq, @comp_proper Obj C z y x g1 g2 geq f1 f2 feq;
    comp_assoc := λ x y z w f g h, symmetry (@comp_assoc Obj C w z y x h g f);

    cat_id := λ x, @cat_id Obj C x;
    cat_id_left := λ x y f, @cat_id_right Obj C y x f;
    cat_id_right := λ x y f, @cat_id_left Obj C y x f
  |}.