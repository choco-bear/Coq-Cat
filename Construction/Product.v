Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

Generalizable All Variables.
Set Transparent Obligations.

(** Being given two categories [C] and [D], we can construct their product category
  * [C × D], which has objects that are pairs of objects in [C] and objects in [D],
  * and morphisms that are pairs of morphisms.
  *)
Program Definition BinaryProductCategory (C D : Category) : Category :=
  {| obj := obj[C] * obj[D]
   ; hom := λ x y, (hom (fst x) (fst y)) * (hom (snd x) (snd y))
   ; homset := λ x y, prod_setoid
   ; id := λ x, (id[fst x], id[snd x])
   ; compose := λ x y z f g, (fst f ∘ fst g, snd f ∘ snd g)

   ; compose_respects := λ x y z f g fg h i hi,
        ( compose_respects (fst f) (fst g) (fst fg) (fst h) (fst i) (fst hi)
        , compose_respects (snd f) (snd g) (snd fg) (snd h) (snd i) (snd hi) )

   ; id_left := λ x y f,
        ( id_left (fst f)
        , id_left (snd f) )
   ; id_right := λ x y f,
        ( id_right (fst f)
        , id_right (snd f) )

   ; comp_assoc := λ x y z w f g h,
        ( comp_assoc (fst f) (fst g) (fst h)
        , comp_assoc (snd f) (snd g) (snd h) )
   ; comp_assoc_sym := λ x y z w f g h,
        ( comp_assoc_sym (fst f) (fst g) (fst h)
        , comp_assoc_sym (snd f) (snd g) (snd h) )
  |}.

Notation "C × D" := (BinaryProductCategory C%category D%category)
  (at level 40, left associativity) : category_scope.

(** The projection functors [Fst : C × D ⟶ C] and [Snd : C × D ⟶ D] map each object
  * [(c, d)] in [C × D] to the object [c] in [C] and to the object [d] in [D],
  * respectively, and each morphism [(f, g)] in [C × D] to the morphism [f] in [C]
  * and to the morphism [g] in [D], respectively.
  *)
Section Projection.
  Context {C D : Category}.

  #[export]
  Program Instance Fst : C × D ⟶ C :=
    {| fobj := λ x, fst x
     ; fmap := λ _ _ f, fst f
    |}.

  #[export]
  Program Instance Snd : C × D ⟶ D :=
    {| fobj := λ x, snd x
     ; fmap := λ _ _ f, snd f
    |}.

  Corollary fst_comp {x y z} (f : y ~{C × D}~> z) (g : x ~{C × D}~> y)
    : fst (f ∘ g) ≡ fst f ∘ fst g.
  Proof. reflexivity. Qed.

  Corollary snd_comp {x y z} (f : y ~{C × D}~> z) (g : x ~{C × D}~> y)
    : snd (f ∘ g) ≡ snd f ∘ snd g.
  Proof. reflexivity. Qed.
End Projection.
#[export] Hint Rewrite @fst_comp @snd_comp : categories normalize.

(** The opposite category of [C × D] is [C^op × D^op]. *)
Lemma BinaryProductCategory_Opposite (C D : Category)
  : (C × D)^op = C^op × D^op.
Proof.
  unfold Opposite, BinaryProductCategory; simpl.
  destruct C, D; simpl. f_equal.
(* SLOW *) Qed.

Section BinaryProductFunctor.
  Program Definition BinaryProductFunctor `(T : D ⟶ B) `(R : D ⟶ C) : D ⟶ B × C :=
    {|  fobj := λ d, (T d, R d) : B × C
      ; fmap := λ x y f, (fmap[T] f, fmap[R] f)
    |}.

  Notation "F × G" := (BinaryProductFunctor F%functor G%functor)
    (at level 40, left associativity) : functor_scope.

  Lemma BinaryProductFunctor_Fst `(T : D ⟶ B) `(R : D ⟶ C)
    : Fst ◯ (T × R) ≡ T.
  Proof. by construct. Qed.

  Lemma BinaryProductFunctor_Snd `(T : D ⟶ B) `(R : D ⟶ C)
    : Snd ◯ (T × R) ≡ R.
  Proof. by construct. Qed.

  Program Definition BinaryProductFunctor_Unique `(T : D ⟶ B) `(R : D ⟶ C)
    (F' : D ⟶ B × C) (HProj1 : Fst ◯ F' ≡ T) (HProj2 : Snd ◯ F' ≡ R)
    : F' ≡ T × R := (_; _).
  Next Obligation.
    isomorphism.
    - exact (HProj1 x : fst (F' x) ~> T x, HProj2 x : snd (F' x) ~> R x).
    - exact ((HProj1 x)⁻¹, (HProj2 x)⁻¹).
    - cat.
    - cat.
  Defined.
End BinaryProductFunctor.

Notation "F × G" := (BinaryProductFunctor F%functor G%functor)
  (at level 40, left associativity) : functor_scope.

(** A bifunctor is any functor from product of two categories, to another category;
  * so we do not formalize it separately. But there are some helper functions
  * related to bifunctors. *)
Section Bifunctor.
  Context {C D E : Category} {F : C × D ⟶ E}.

  Definition biobj (x : C) (y : D) : E := fobj[F] (x, y).

  Definition bimap {x1 x2 : C} {y1 y2 : D}
    (f : x1 ~> x2) (g : y1 ~> y2) : F (x1, y1) ~{E}~> F (x2, y2) :=
    @fmap (C × D) E F (x1, y1) (x2, y2) (f, g).

  #[export]
  Program Instance bimap_respects {x1 x2 : C} {y1 y2 : D}
    : Proper (equiv ==> equiv ==> equiv) (@bimap x1 x2 y1 y2) :=
      λ f1 f2 Hf g1 g2 Hg,
        @fmap_respects (C × D) E F (x1, y1) (x2, y2) (f1, g1) (f2, g2) (Hf, Hg).

  Corollary bimap_id_id {x : C} {y : D} : bimap (id[x]) (id[y]) ≡ id.
  Proof. by unfold bimap. Qed.
    
  Corollary bimap_comp {x1 x2 x3 : C} {y1 y2 y3 : D}
    (f1 : x2 ~> x3) (f2 : x1 ~> x2)
    (g1 : y2 ~> y3) (g2 : y1 ~> y2)
    : bimap (f1 ∘ f2) (g1 ∘ g2) ≡ bimap f1 g1 ∘ bimap f2 g2.
  Proof. by unfold bimap; rewrite <- fmap_comp. Qed.

  Corollary bimap_comp_left_id {x1 x2 x3 : C} {y : D}
    (f : x2 ~> x3) (g : x1 ~> x2)
    : bimap (f ∘ g) (id[y]) ≡ bimap f (id[y]) ∘ bimap g (id[y]).
  Proof. by rewrite <- bimap_comp. Qed.

  Corollary bimap_comp_right_id {x : C} {y1 y2 y3 : D}
    (f : y2 ~> y3) (g : y1 ~> y2)
    : bimap (id[x]) (f ∘ g) ≡ bimap (id[x]) f ∘ bimap (id[x]) g.
  Proof. by rewrite <- bimap_comp. Qed.

  Corollary bimap_id_right_left {x1 x2 : C} {y1 y2 : D}
    (f : x1 ~> x2) (g : y1 ~> y2)
    : bimap f g ≡ bimap f id ∘ bimap id g.
  Proof. by rewrite <- bimap_comp. Qed.

  Corollary bimap_id_left_right {x1 x2 : C} {y1 y2 : D}
    (f : x1 ~> x2) (g : y1 ~> y2)
    : bimap f g ≡ bimap id g ∘ bimap f id.
  Proof. by rewrite <- bimap_comp. Qed.
End Bifunctor.

#[export] Hint Rewrite @bimap_id_id : categories.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

Ltac bimap_left :=
  apply bimap_respects; [reflexivity|].

Ltac bimap_right :=
  apply bimap_respects; [|reflexivity].

Program Definition ProductCategory [I : Type] (C : I → Category) : Category :=
  {|  obj := ∀ i, C i
    ; hom := λ x y, ∀ i, (x i) ~{C i}~> (y i)
    ; homset := λ x y, funext_Setoid I (λ i, (x i) ~{C i}~> (y i))

    ; id := λ x i, id
    ; compose := λ x y z f g i, f i ∘ g i

    ; compose_respects := λ x y z f g fg h i hi,
        λ j, compose_respects (f j) (g j) (fg j) (h j) (i j) (hi j)

    ; id_left := λ x y f,
        λ j, id_left (f j)
    ; id_right := λ x y f,
        λ j, id_right (f j)

    ; comp_assoc := λ x y z w f g h,
        λ j, comp_assoc (f j) (g j) (h j)
    ; comp_assoc_sym := λ x y z w f g h,
        λ j, comp_assoc_sym (f j) (g j) (h j)
  |}.

Notation "∏ C" := (ProductCategory (C%category))
  (at level 41, right associativity) : category_scope.

Section ProductCategoryProjection.
  Context {I : Type} {C : I → Category}.

  #[export]
  Program Instance Project (j : I) : ∏ C ⟶ (C j) :=
    {|  fobj := λ x, x j
      ; fmap := λ x y f, f j
    |}.

  Corollary project_comp {j : I} {x y z : ∏ C}
    (f : y ~{∏ C}~> z) (g : x ~{∏ C}~> y) : (f ∘ g) j ≡ f j ∘ g j.
  Proof. reflexivity. Qed.
End ProductCategoryProjection.
#[export] Hint Rewrite @project_comp : categories normalize.

(** The opposite category of [∏ C] is [∏ (fun i => (C i)^op)]. *)
Lemma ProductCategory_Opposite {I : Type} (C : I → Category)
  : (∏ C)^op = ∏ (fun i => (C i)^op).
Proof. reflexivity. Qed.

Section ProductFunctor.
  Program Definition ProductFunctor [I : Type] `(F : ∀ i : I, D ⟶ C i) : D ⟶ ∏ C :=
    {|  fobj := λ x i, F i x
      ; fmap := λ x y f i, fmap[F i] f
    |}.

  Notation "'Π' F" := (ProductFunctor F%functor)
    (at level 41, right associativity) : functor_scope.

  Lemma ProductFunctor_Project [I : Type]
    `(F : ∀ i : I, D ⟶ C i) (j : I) : Project j ◯ (Π F) ≡ F j.
  Proof. by construct. Qed.

  Program Definition ProductFunctor_Unique [I : Type]
    `(F : ∀ i : I, D ⟶ C i) (F' : D ⟶ ∏ C)
    (HProj : ∀ j : I, Project j ◯ F' ≡ F j) : F' ≡ Π F := (_; _).
  Next Obligation.
    isomorphism.
    - exact (λ i, `1 (HProj i) x).
    - exact (λ i, (`1 (HProj i) x)⁻¹).
    - cat.
    - cat.
  Defined.
  Next Obligation. by pose (`2 (HProj x0)). Defined.
End ProductFunctor.