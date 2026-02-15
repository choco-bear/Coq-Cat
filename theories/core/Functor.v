Require Import Category CommonTactics.

Structure Functor `{C : Category ObjC} `{D : Category ObjD} := mk_Functor {
  #[export] fobj :> ObjC → ObjD;
  fmap {x y} (f : x ~> y) : fobj x ~> fobj y;
  #[export] fmap_proper {x y} :: Proper ((≡) ==> (≡)) (@fmap x y);
  fmap_id x : fmap id[x] ≡[D] id;
  fmap_comp {x y z} (f : y ~> z) (g : x ~> y) : fmap (f ∘ g) ≡[D] fmap f ∘ fmap g;
}.
Global Hint Rewrite @fmap_id @fmap_comp : normalize.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.
Bind Scope functor_scope with Functor.

Arguments Functor {_%_type_scope} C%_category_scope {_%_type_scope} D%_category_scope.
Arguments fmap {_%_type_scope C%_category_scope _%_type_scope D%_category_scope} F%_functor_scope {x y}%_object_scope f%_morphism_scope : rename.
Arguments fmap_proper {x y}%_object_scope (f g)%_morphism_scope EQ : rename.

Notation "F # f" := (fmap F%functor f%morphism) (at level 30, right associativity) : morphism_scope.
Notation "C ⟶ D" := (Functor C%category D%category) (at level 60, right associativity) : type_scope.

Program Definition IdFunctor `(C : Category Obj) : C ⟶ C :=
  {|
    fobj := λ x, x;
    fmap := λ _ _ f, f;
  |}.

Program Definition FunctorCompose
  `(F : (C : Category ObjC) ⟶ (D : Category ObjD)) `(G : (B : Category ObjB) ⟶ C) : B ⟶ D :=
  {|
    fobj := F ∘ G;
    fmap := λ _ _ f, (F # G # f)%morphism
  |}.

Program Definition ConstantFunctor `{C : Category ObjC} `{D : Category ObjD} (v : ObjD) : C ⟶ D :=
  {|
    fobj := λ _, v;
    fmap := λ _ _ _, id[v]%morphism
  |}.

Notation "'Id'" := (IdFunctor _) (only parsing) : functor_scope.
Notation "'Id[' C ']'" := (IdFunctor C%category) (at level 7, no associativity) : functor_scope.

Infix "∘" := FunctorCompose : functor_scope.

Notation ".↦ v" := (ConstantFunctor v) (at level 8, right associativity) : functor_scope.

Class Faithful `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) :=
  { faithful {x y} (f g : x ~> y) : F # f ≡[D] F # g → f ≡ g }.

Class Full `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) :=
  { full {x y} (h : F x ~> F y) : ∃ (f : x ~> y), F # f ≡[D] h }.

Class FullyFaithful `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) :=
  {
    #[export] fully_faithful_faithful :: Faithful F;
    #[export] fully_faithful_full :: Full F;
  }.