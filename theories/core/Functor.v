Require Import Category CommonTactics.

Structure Functor `{C : Category ObjC} `{D : Category ObjD} := mk_Functor {
  fobj :> ObjC → ObjD;
  fmap {x y} (f : x ~> y) : fobj x ~> fobj y;
  fmap_id x : fmap id[x] =[D] id;
  fmap_comp {x y z} (f : y ~> z) (g : x ~> y) : fmap (f ∘ g) =[D] fmap f ∘ fmap g;
}.
Global Hint Rewrite @fmap_id @fmap_comp : normalize.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.
Bind Scope functor_scope with Functor.

Arguments Functor {_%_type_scope} C%_category_scope {_%_type_scope} D%_category_scope.
Arguments mk_Functor {_%_type_scope _%_category_scope _%_type_scope _%_category_scope} (_ _ _ _)%_function_scope.
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

Notation "'id'" := (IdFunctor _) (only parsing) : functor_scope.
Notation "'id[' C ']'" := (IdFunctor C%category) (at level 9, no associativity, format "id[ C ]") : functor_scope.

Notation "F ∘ G" := (FunctorCompose F%functor G%functor) : functor_scope.

Notation ".↦ v" := (ConstantFunctor v) (at level 8, right associativity) : functor_scope.

Section FunctorApplications.
  Context `{C : Category ObjC}.
  Lemma Id_fobj : fobj id[C] = Datatypes.id.
  Proof. reflexivity. Qed.
  Lemma Id_fmap {x y : ObjC} : fmap id[C] = Datatypes.id :> (_ → x ~> y).
  Proof. reflexivity. Qed.

  Context `{D : Category ObjD}.
  Lemma Const_fobj (v : ObjD) : fobj (.↦ v) = λ _, v.
  Proof. reflexivity. Qed.
  Lemma Const_fmap (v : ObjD) {x y : ObjC} : fmap (.↦ v) = (λ _, id[v]%morphism) :> (x ~> y → _).
  Proof. reflexivity. Qed.

  Context `{B : Category ObjB}.
  Lemma Comp_fobj (F : C ⟶ D) (G : B ⟶ C) : fobj (F ∘ G) = F ∘ G.
  Proof. reflexivity. Qed.
  Lemma Comp_fmap (F : C ⟶ D) (G : B ⟶ C) {x y : ObjB} : 
    fmap (F ∘ G) = fmap F ∘ fmap G :> (x ~> y → _).
  Proof. reflexivity. Qed.
End FunctorApplications.
Global Opaque IdFunctor ConstantFunctor FunctorCompose.

Section FunctorProperty.
  Context `{C : Category ObjC} `{D : Category ObjD} (F : C ⟶ D).

  Class Faithful := {
    #[export] faithful {x y : ObjC} :: Inj (=) (=) (fmap F : x ~> y → _)
  }.

  Class Full := {
    #[export] full {x y : ObjC} :: Surj (=) (fmap F : x ~> y → _)
  }.

  Class FullyFaithful :=
    {
      #[export] fully_faithful_faithful :: Faithful;
      #[export] fully_faithful_full     :: Full;
    }.

  Class IsFunctorIso :=
    {
      inverse_functor   : D ⟶ C;
      inv_functor_left  : (inverse_functor ∘ F = id[C])%functor;
      inv_functor_right : (F ∘ inverse_functor = id[D])%functor;
    }.
End FunctorProperty.

Arguments inverse_functor {_%_type_scope C%_category_scope _%_type_scope D%_category_scope} F%_functor_scope {FunctorIso} : rename, simpl never.

Notation "F '⁻¹'" := (inverse_functor F%functor) (at level 7, left associativity, format "F ⁻¹") : functor_scope.