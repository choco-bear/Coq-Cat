Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** Functors map objects and morphisms between categories, where such mappings
  * preserve equivalences and basic categorical structure (identity and
  * composition). Note that there are many species of functor, one each for the
  * various categorical structures (included below), for example, the
  * `CartesianFunctor` that maps products to products and preserves all its
  * structural properties and laws.
  *)

Class Functor@{o1 h1 p1 o2 h2 p2}
  {C : Category@{o1 h1 p1}} {D : Category@{o2 h2 p2}} :=
  { fobj : C → D
  ; fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y

  ; fmap_respects : ∀ x y,
      Proper@{h2 p2} (respectful@{h1 p1 h2 p2 h2 p2}
                        equiv@{h1 p1} equiv@{h2 p2}) (@fmap x y)

  ; fmap_id {x : C} : fmap id[x] ≡ id[fobj x]
  ; fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
      fmap (f ∘ g) ≡ fmap f ∘ fmap g
  }.
#[export] Existing Instance fmap_respects.

Declare Scope functor_scope.
Declare Scope functor_type_scope.
Bind Scope functor_scope with Functor.
Delimit Scope functor_type_scope with functor_type.
Delimit Scope functor_scope with functor.
Open Scope functor_type_scope.
Open Scope functor_scope.

(** Functors used as functions map objects of categories, similar to the way type
  * constructors behave in Haskell. We cannot, unfortunately, have a similar
  * coercion for morphisms, because coercions cannot be bound to scopes.
  *)
Coercion fobj : Functor >-> Funclass.

Notation "C ⟶ D" := (@Functor C%category D%category)
  (at level 90, right associativity) : functor_type_scope.

Arguments fmap {C%_category D%_category Functor%_functor x%_object y%_object}
  f%_morphism.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 0, format "fobj[ F ]") : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 0, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories.

(** [AFunctor] allows the object mapping to be stated explicitly. *)
Section AFunctor.
  Context {C D : Category}.

  Class AFunctor (F : C → D) : Type :=
    { a_fmap {x y : C} (f : x ~> y) : F x ~> F y

    ; a_fmap_respects {x y : C} : Proper (equiv ==> equiv) (@a_fmap x y)

    ; a_fmap_id {x : C} : a_fmap id[x] ≡ id[F x]
    ; a_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
        a_fmap (f ∘ g) ≡ a_fmap f ∘ a_fmap g
    }.
  #[export] Existing Instance a_fmap_respects.

  Definition FromAFunctor `(AFunctor F) : C ⟶ D :=
    {| fobj := λ x, F x
     ; fmap := @a_fmap F _
     ; fmap_respects := @a_fmap_respects F _
     ; fmap_id := @a_fmap_id F _
     ; fmap_comp := @a_fmap_comp F _
    |}.

  Coercion FromAFunctor : AFunctor >-> Functor.

  Definition ToAFunctor (F : C ⟶ D) : AFunctor F :=
    {| a_fmap := @fmap _ _ F
     ; a_fmap_respects := @fmap_respects _ _ F
     ; a_fmap_id := @fmap_id _ _ F
     ; a_fmap_comp := @fmap_comp _ _ F
    |}.

  Corollary FromAFunctor_ToAFunctor {F}
    : FromAFunctor (ToAFunctor F) = F.
  Proof. reflexivity. Qed.

  Corollary ToAFunctor_FromAFunctor `{H : AFunctor F}
    : ToAFunctor (FromAFunctor H) = H.
  Proof. reflexivity. Qed.
End AFunctor.

Section Definitions.
  Program Definition Functor_Compose {C D E : Category} (F : D ⟶ E) (G : C ⟶ D)
    : C ⟶ E :=
      {| fobj := λ x, fobj[F] (fobj[G] x)
       ; fmap := λ x y f, fmap[F] (fmap[G] f)
      |}.
  Next Obligation. proper. now rewrites. Qed.
  Next Obligation. now rewrite <-!fmap_comp. Qed.

  Program Definition Functor_Identity {C : Category} : C ⟶ C :=
    {| fobj := Datatypes.id
     ; fmap := λ _ _, Datatypes.id
    |}.
End Definitions.

Notation "F '○' G" := (Functor_Compose F G)
  (at level 40, left associativity) : functor_scope.

Notation "'Id'" := Functor_Identity : functor_scope.
Notation "'Id[' C ']'" := (@Functor_Identity C)
  (at level 0, format "Id[ C ]", only parsing) : functor_scope.