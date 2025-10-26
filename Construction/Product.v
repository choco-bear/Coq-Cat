Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

(** Being given two categories [C] and [D], we can construct their product category
  * [C × D], which has objects that are pairs of objects in [C] and objects in [D],
  * and morphisms that are pairs of morphisms.
  *)
Program Definition Product (C D : Category) : Category :=
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

Notation "C × D" := (Product C D) (at level 40, left associativity) : category_scope.

(** The projection functors [Fst : C × D ⟶ C] and [Snd : C × D ⟶ D] map each object
  * [(c, d)] in [C × D] to the object [c] in [C] and to the object [d] in [D],
  * respectively, and each morphism [(f, g)] in [C × D] to the morphism [f] in [C]
  * and to the morphism [g] in [D], respectively.
  *)
Section Projection.
  Context {C D : Category}.

  Program Definition Fst : C × D ⟶ C :=
    {| fobj := λ x, fst x
     ; fmap := λ _ _ f, fst f
    |}.

  Program Definition Snd : C × D ⟶ D :=
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
#[export] Hint Rewrite @fst_comp @snd_comp : categories.

(** The opposite category of [C × D] is [C^op × D^op]. *)
Lemma Product_Opposite (C D : Category)
  : (C × D)^op = C^op × D^op.
Proof.
  unfold Opposite, Product; simpl.
  destruct C, D; simpl. f_equal.
(* SLOW *) Qed.