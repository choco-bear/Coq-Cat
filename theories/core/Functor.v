Require Import Category CommonTactics.

Structure Functor `{C : Category ObjC} `{D : Category ObjD} := mk_Functor {
  #[export] fobj :> ObjC → ObjD;
  fmap {x y} (f : x ~> y) : fobj x ~> fobj y;
  fmap_id x : fmap id[x] =[D] id;
  fmap_comp {x y z} (f : y ~> z) (g : x ~> y) : fmap (f ∘ g) =[D] fmap f ∘ fmap g;
}.
Global Hint Rewrite @fmap_id @fmap_comp : normalize.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.
Bind Scope functor_scope with Functor.

Arguments Functor {_%_type_scope} C%_category_scope {_%_type_scope} D%_category_scope.
Arguments fobj {_%_type_scope C%_category_scope _%_type_scope D%_category_scope} F%_functor_scope x%_object_scope : rename, simpl never.
Arguments fmap {_%_type_scope C%_category_scope _%_type_scope D%_category_scope} F%_functor_scope {x y}%_object_scope f%_morphism_scope : rename, simpl never.

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
Notation "'Id[' C ']'" := (IdFunctor C%category) (at level 7, no associativity, format "Id[ C ]") : functor_scope.

Notation "F ∘ G" := (FunctorCompose F%functor G%functor) : functor_scope.

Notation ".↦ v" := (ConstantFunctor v) (at level 8, right associativity) : functor_scope.

Section FunctorApplications.
  Context `{C : Category ObjC}.
  Lemma Id_fobj (x : ObjC) : fobj Id[C] x = x.
  Proof. reflexivity. Qed.
  Lemma Id_fmap {x y : ObjC} (f : x ~> y) : Id[C] # f =[C] f.
  Proof. reflexivity. Qed.

  Context `{D : Category ObjD}.
  Lemma Const_fobj (v : ObjD) (x : ObjC) : fobj (.↦ v) x = v.
  Proof. reflexivity. Qed.
  Lemma Const_fmap (v : ObjD) {x y : ObjC} (f : x ~> y) : (.↦ v) # f =[D] id[v].
  Proof. reflexivity. Qed.

  Context `{B : Category ObjB}.
  Lemma Comp_fobj (F : C ⟶ D) (G : B ⟶ C) (x : ObjB) : fobj (F ∘ G) x = F (G x).
  Proof. reflexivity. Qed.
  Lemma Comp_fmap (F : C ⟶ D) (G : B ⟶ C) {x y : ObjB} (f : x ~> y) : 
    (F ∘ G) # f =[D] F # (G # f).
  Proof. reflexivity. Qed.
End FunctorApplications.
Global Opaque IdFunctor ConstantFunctor FunctorCompose.

Class Faithful `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) :=
  { faithful {x y} (f g : x ~> y) : F # f =[D] F # g → f = g }.

Class Full `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) :=
  { full {x y} (h : F x ~> F y) : ∃ (f : x ~> y), F # f =[D] h }.

Class FullyFaithful `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D) :=
  {
    #[export] fully_faithful_faithful :: Faithful F;
    #[export] fully_faithful_full :: Full F;
  }.