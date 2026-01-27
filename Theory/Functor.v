Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Reserved Infix "◯" (at level 40, left associativity).

Generalizable All Variables.

(** Functors map objects and morphisms between categories, where such mappings
  * preserve equivalences and basic categorical structure -- identity and
  * composition.
  *)

Class Functor {C : Category} {D : Category} : Type :=
    { fobj : C → D
    ; fmap {x y : C} (f : x ~> y) : fobj x ~> fobj y

    ; fmap_respects : ∀ x y,
        Proper (respectful equiv equiv) (@fmap x y)

    ; fmap_id {x : C} : fmap (@id C x) ≡ id
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

Arguments fobj {C D}%_category {FUNCTOR}%_functor x%_object : rename.
Arguments fmap {C D}%_category {FUNCTOR}%_functor {x y}%_object f%_morphism : rename, simpl never.

Infix "<$>" := fmap
  (at level 29, left associativity, only parsing) : morphism_scope.
Infix "<$[ F ]>" := (@fmap _ _ F%functor _ _)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <$ m" := (fmap (Basics.const x) m)
  (at level 29, left associativity, only parsing) : morphism_scope.
Notation "x <&> f" := (fmap f x)
  (at level 29, left associativity, only parsing) : morphism_scope.

Notation "fobj[ F ]" := (@fobj _ _ F%functor)
  (at level 0, only parsing) : object_scope.
Notation "fmap[ F ]" := (@fmap _ _ F%functor _ _)
  (at level 0, format "fmap[ F ]") : morphism_scope.

#[export] Hint Rewrite @fmap_id : categories normalize.
(** Prefer contracting composed fmaps into a single fmap to avoid
  * expansion/contraction cycles when autorewrite runs on polymorphic/category-heavy
  * terms. Orienting this rewrite to the <- direction makes autorewrite reduce term
  * size instead of expanding it, avoiding potential non-termination. *)
#[export] Hint Rewrite <- @fmap_comp : categories.
#[export] Hint Rewrite @fmap_comp : normalize.
#[export] Hint Resolve fmap : category_laws.

Definition fmap_simpl {C : Category} {D : Category} `(f : x ~{C}~> y) fobj fmap fmap_respects fmap_id fmap_comp
  : fmap[Build_Functor C D fobj fmap fmap_respects fmap_id fmap_comp] f = fmap _ _ f := eq_refl.
#[export] Hint Rewrite @fmap_simpl : categories normalize.

(** [AFunctor] allows the object mapping to be stated explicitly. *)
Section AFunctor.
  Context {C : Category} {D : Category}.

  Class AFunctor (F : C → D) : Type :=
    { a_fmap {x y : C} (f : x ~> y) : F x ~> F y

    ; a_fmap_respects {x y : C} :
        Proper (respectful equiv equiv) (@a_fmap x y)

    ; a_fmap_id {x : C} : a_fmap id[x] ≡ id[F x]
    ; a_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
        a_fmap (f ∘ g) ≡ a_fmap f ∘ a_fmap g
    }.
  #[export] Existing Instance a_fmap_respects.

  Definition FromAFunctor `(AFunctor F) : C ⟶ D :=
    {|  fobj := λ x, F x
      ; fmap := @a_fmap F _
      ; fmap_respects := @a_fmap_respects F _
      ; fmap_id := @a_fmap_id F _
      ; fmap_comp := @a_fmap_comp F _
    |}.

  Coercion FromAFunctor : AFunctor >-> Functor.

  Definition ToAFunctor (F : C ⟶ D) : AFunctor F :=
    {|  a_fmap := @fmap _ _ F
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

Definition Functor_Compose {C : Category} {D : Category} {E : Category}
                           (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E :=
  {|  fobj := λ x, fobj[F] (fobj[G] x)
    ; fmap := λ x y f, fmap[F] (fmap[G] f)

    ; fmap_respects :=
      λ x y f g EQ, fmap_respects _ _ _ _ (fmap_respects _ _ _ _ EQ)
  
    ; fmap_id   := λ x, transitivity (fmap_respects _ _ _ _ fmap_id) fmap_id
    ; fmap_comp := λ x y z f g, transitivity (fmap_respects _ _ _ _ (fmap_comp f g)) (fmap_comp _ _)
  |}.
  
Notation "F '◯' G" := (Functor_Compose F G)
  (at level 40, left associativity) : functor_scope.

Section Compose.
  Context {C : Category} {D : Category} {E : Category}.
  Context (F : D ⟶ E) (G : C ⟶ D).

  Definition fobj_compose x : (F ◯ G) x = F (G x) := eq_refl.

  Definition fmap_compose `(f : x~{C}~>y) : fmap[F ◯ G] f = fmap[F] (fmap[G] f) := eq_refl.
End Compose.
#[export] Hint Rewrite @fobj_compose @fmap_compose : categories normalize.

Definition Functor_Identity {C : Category} : C ⟶ C :=
  {|  fobj := Datatypes.id
    ; fmap := λ _ _, Datatypes.id

    ; fmap_respects := λ x y, subrelation_id_proper (subrelation_refl equiv)

    ; fmap_id   := λ x, @Equivalence_Reflexive _ equiv setoid_equiv _
    ; fmap_comp := λ x y z f g, @Equivalence_Reflexive _ equiv setoid_equiv _
  |}.

Notation "'Id'" := Functor_Identity (only parsing) : functor_scope.
Notation "'Id[' C ']'" := (@Functor_Identity C)
  (at level 0, format "Id[ C ]") : functor_scope.

Section Identity.
  Context {C : Category}.

  Definition fobj_identity x : Id x = x := eq_refl.

  Definition fmap_identity `(f : x ~> y) : fmap[Id] f = f := eq_refl.
End Identity.
#[export] Hint Rewrite @fobj_identity @fmap_identity : categories normalize.

Definition constant_Functor {C : Category} {D : Category} (v : D) : C ⟶ D :=
  {|  fobj := λ _, v
    ; fmap := λ _ _ _, id[v]

    ; fmap_respects := λ _ _ _ _ _, reflexivity id[v]

    ; fmap_id := λ _, reflexivity id[v]
    ; fmap_comp := λ _ _ _ _ _, symmetry (id_right id[v])
  |}.

Notation "'Const' v" := (constant_Functor v)
  (at level 0,  right associativity, only parsing) : functor_scope.
Notation "'Const[' C ']' v" := (@constant_Functor C _ v)
  (at level 0, format "Const[ C ]  v") : functor_scope.

Section Const.
  Context {C : Category} {D : Category} (v : D).

  Definition fobj_const x : Const v x = v := eq_refl.

  Definition fmap_const `(f : x ~{C}~> y) : fmap[Const v] f = id := eq_refl.
End Const.
#[export] Hint Rewrite @fobj_const @fmap_const : categories normalize.

(** A functor [F] is said to be faithful if it is injective on the morphism
  * level, i.e., for any two morphisms [f, g : x ~> y] in [C], if
  * [fmap[F] f ≡ fmap[F] g], then [f ≡ g].
  *)
Class Faithful `(F : C ⟶ D) :=
  { faithful : ∀ {x y : C} (f g : x ~> y),
      fmap[F] f ≡ fmap[F] g → f ≡ g
  }.

(** A functor [F : C ⟶ D] is said to be full if for any morphism [g : F x ~> F y] in
  * [D], there exists a morphism [f : x ~> y] in [C] such that [fmap[F] f ≡ g].
  *)
Class Full `(F : C ⟶ D) :=
  { full : ∀ {x y : C} (g : fobj[F] x ~> fobj[F] y),
      ∃ f : x ~> y, fmap[F] f ≡ g
  }.

Instance Faithful_Injective `(F : C ⟶ D) `{@Faithful _ _ F} {x y : C}
  : Injective (@fmap _ _ F x y).
Proof. construct. now apply faithful. Defined.

Instance Full_Surjective `(F : C ⟶ D) `{@Full _ _ F} {x y : C}
  : Surjective (@fmap _ _ F x y).
Proof. construct. now apply full. Defined.

Lemma fully_faithful `(F : C ⟶ D) `{@Full _ _ F} `{@Faithful _ _ F}
    : ∀ x y, F x ≅ F y → x ≅ y.
Proof.
  ii. remember (full X) as to. remember (full X⁻¹) as from. isomorphism.
  - exact (`1 to).
  - exact (`1 from).
  - destruct to, from. s. apply faithful.
    by normalize; rewrite e, e0.
  - destruct to, from. s. apply faithful.
    by normalize; rewrite e, e0.
Qed.

(** Lemmas for automatic simplfication *)
Section Simpl.
  Context {C : Category}.
  Context {D : Category}.

  Lemma simpl_1 {x y : C} {z : D} (F : C ⟶ D) (f : F y ~> z) (g : x ≅ y)
    : f ∘ fmap[F] g ∘ fmap[F] g⁻¹ ≡ f.
  Proof. by rewrite <-comp_assoc, <-fmap_comp, iso_to_from. Qed.

  Lemma simpl_2 {x y : C} {z : D} (F : C ⟶ D) (f : F y ~> z) (g : y ≅ x)
    : f ∘ fmap[F] g⁻¹ ∘ fmap[F] g ≡ f.
  Proof. by rewrite <-comp_assoc, <-fmap_comp, iso_from_to. Qed.
End Simpl.
#[export] Hint Rewrite @simpl_1 @simpl_2 : categories normalize.