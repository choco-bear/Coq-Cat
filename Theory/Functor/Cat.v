Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Instance.Cat.
From Category.Construction Require Import Product Opposite.

Generalizable All Variables.

(** This file defines important functors related to the category of categories. *)

(** Opposite functor is the functor mapping each category to its opposite category. *)
Section OppositeFunctor.
  Program Definition OppositeTranslate {B : Category} {C : Category} (T : B ⟶ C) : B^op ⟶ C^op :=
    {|  fobj := λ x : obj[B^op], T x : obj[C^op]
      ; fmap := λ x y f, fmap[T] f
    |}.

  Definition fobj_OppositeTranslate {B : Category} {C : Category} (T : B ⟶ C) x
    : OppositeTranslate T x = T x := eq_refl.

  Definition fmap_OppositeTranslate {B : Category} {C : Category} (T : B ⟶ C) `(f : x ~{B^op}~> y)
    : fmap[OppositeTranslate T] f = fmap[T] f := eq_refl.
  Hint Rewrite @fmap_OppositeTranslate : categories normalize.

  Program Definition OppositeFunctor : Cat ⟶ Cat :=
    {|  fobj := λ C : Cat, C^op : Cat
      ; fmap := @OppositeTranslate
    |}.
  Next Obligation.
    proper; construct. 
    1,2: now natural_transform; ss; try apply component, X; cat; normalize.
    all: cat_simpl.
  Qed.
  Next Obligation. by functor_equiv_solver. Qed.
  Next Obligation. by functor_equiv_solver. Qed.

  Definition fobj_OppositeFunctor x : OppositeFunctor x = x^op := eq_refl.

  Definition fmap_OppositeFunctor `(f : x ~> y) : fmap[OppositeFunctor] f = OppositeTranslate f := eq_refl.
End OppositeFunctor.
(* #[export] Arguments OppositeTranslate {B C}%_category (T)%_functor : simpl never. *)
(* #[export] Arguments OppositeFunctor : simpl never. *)
#[export] Hint Rewrite @fobj_OppositeTranslate @fmap_OppositeTranslate
                       @fobj_OppositeFunctor @fmap_OppositeFunctor
                       : categories normalize.

Notation "'↥'" := OppositeTranslate : functor_scope.
Notation "'↥[' B ',' C ']'" := (@OppositeTranslate B%category C%category) (only parsing) : functor_scope.
Notation "'(-)^op'" := OppositeFunctor : functor_scope.


(** Fun functor is the bifunctor mapping each pair [(A,B)] of categories to the category
  * [Fun[A,B]].
  *)
Section FunBiFunctor.
  Notation "'U'" := (Cat^op × Cat)%category.

  Definition FunBiFunctor_fobj := λ`(A,B) : obj[U], Fun[A,B] : Cat.
  
  Definition FunBiFunctor_fmap {x y : obj[U]} (f : x ~> y)
    : FunBiFunctor_fobj x ~> FunBiFunctor_fobj y.
  Proof.
    do 2 cat. srapply FromAFunctor; try exact (λ X, f0 ◯ X ◯ f).
    construct; [exact (_ ▪ f1 ▪ _)|proper; rewrites|..]; by ss.
  Defined.
  Arguments FunBiFunctor_fmap : simpl never.

  Definition fobj_FunBiFunctor_fmap `(F1 : C1 ~{Cat^op}~> D1) `(F2 : C2 ~{Cat}~> D2) T
    : FunBiFunctor_fmap ((F1, F2) : (C1, C2) ~{U}~> (D1, D2)) T = F2 ◯ T ◯ F1 := eq_refl.

  Definition fmap_FunBiFunctor_fmap `(F1 : C1 ~{Cat^op}~> D1) `(F2 : C2 ~{Cat}~> D2) `(τ : T1 ⟹ T2)
    : fmap[FunBiFunctor_fmap ((F1, F2) : (C1, C2) ~{U}~> (D1, D2))] τ = NaturalTransform_id ▪ τ ▪ NaturalTransform_id := eq_refl.
  Hint Rewrite @fmap_FunBiFunctor_fmap : categories normalize.

  Local Obligation Tactic := idtac.
  Program Definition FunBiFunctor : U ⟶ Cat :=
    {|  fobj := FunBiFunctor_fobj
      ; fmap := @FunBiFunctor_fmap
    |}.
  Next Obligation.
    proper; ss; construct; ss.
    - natural_transform; ss; try exact ((to b) ▪ _ ▪ (to a)).
      ss; normalize; cat. now rewrite naturality.
    - natural_transform; ss; try exact ((from b) ▪ _ ▪ (from a)).
      ss; normalize; cat. now rewrite naturality.
    - by ss; normalize.
    - by ss; normalize.
  Qed.
  Next Obligation. by ss; cat; functor_equiv_solver. Qed.
  Next Obligation. by ss; cat; functor_equiv_solver. Qed.
  (* #[export] Arguments FunBiFunctor : simpl never. *)

  Definition fobj_FunBiFunctor C D : FunBiFunctor (C,D) = Fun[C,D] := eq_refl.

  Definition fmap_FunBiFunctor `(f : x ~> y) : fmap[FunBiFunctor] f = FunBiFunctor_fmap f := eq_refl.
End FunBiFunctor.
#[export] Hint Rewrite @fobj_FunBiFunctor_fmap @fmap_FunBiFunctor_fmap
                       @fobj_FunBiFunctor @fmap_FunBiFunctor
                       : categories normalize.

Notation "'Fun[-,-]'" := FunBiFunctor : functor_scope.
Notation "'Fun[' C ',-]'" :=
  (FunBiFunctor ◯ (Const (C%category : Cat^op) × Id)) : functor_scope.
Notation "'Fun[-,' D ']'" :=
  (FunBiFunctor ◯ (Id × Const D%category)) : functor_scope.


(** Prod functor is the bifunctor mapping each pair [(A,B)] of categories to the category
  * [A × B].
  *)
Section BinaryProductBiFunctor.
  Definition BinaryProductBiFunctor_fobj := λ`(A,B) : obj[Cat × Cat], (A × B)%category : Cat.

  Definition BinaryProductBiFunctor_fmap {x y : obj[Cat × Cat]} (f : x ~> y)
    : BinaryProductBiFunctor_fobj x ~> BinaryProductBiFunctor_fobj y.
  Proof.
    do 2 cat. srapply FromAFunctor; try exact (λ`(a,b), (f a, f0 b)).
    construct; first [by cat|proper; rewrites]; done.
  Defined.
  Arguments BinaryProductBiFunctor_fmap : simpl never.

  Definition fobj_BinaryProductBiFunctor_fmap `(F1 : C1 ⟶ D1) `(F2 : C2 ⟶ D2) (x1 : C1) (x2 : C2)
    : BinaryProductBiFunctor_fmap ((F1, F2) : (C1, C2) ~{Cat × Cat}~> (D1, D2)) (x1, x2) = (F1 x1, F2 x2) := eq_refl.

  Definition fmap_BinaryProductBiFunctor_fmap `(F1 : C1 ⟶ D1) `(F2 : C2 ⟶ D2) `(f1 : x1 ~{C1}~> y1) `(f2 : x2 ~{C2}~> y2)
    : fmap[BinaryProductBiFunctor_fmap ((F1, F2) : (C1, C2) ~{Cat × Cat}~> (D1, D2))] ((f1, f2) : (x1, x2) ~{C1 × C2}~> (y1, y2)) = (fmap[F1] f1, fmap[F2] f2) := eq_refl.

  Local Obligation Tactic := idtac.
  Program Definition BinaryProductBiFunctor : Cat × Cat ⟶ Cat :=
    {|  fobj := BinaryProductBiFunctor_fobj
      ; fmap := @BinaryProductBiFunctor_fmap
    |}.
  Next Obligation.
    proper; ss; construct; ss; try now natural_transform; ss; do 2 cat; ss; rewrite naturality.
    all: do 2 cat.
  Qed.
  Next Obligation. by ss; cat; functor_equiv_solver. Qed.
  Next Obligation. by ss; cat; functor_equiv_solver. Qed.
  (* #[export] Arguments BinaryProductBiFunctor : simpl never. *)

  Definition fobj_BinaryProductBiFunctor x y : BinaryProductBiFunctor (x,y) = (x × y)%category := eq_refl.

  Definition fmap_BinaryProductBiFunctor `(f : x ~> y) : fmap[BinaryProductBiFunctor] f = BinaryProductBiFunctor_fmap f := eq_refl.
End BinaryProductBiFunctor.
#[export] Hint Rewrite @fobj_BinaryProductBiFunctor_fmap @fmap_BinaryProductBiFunctor_fmap
                       @fobj_BinaryProductBiFunctor @fmap_BinaryProductBiFunctor : categories normalize.

Notation "'(-×-)'" := BinaryProductBiFunctor : functor_scope.
Notation "'(-×' C ')'" := (BinaryProductBiFunctor ◯ (Id × Const C)) : functor_scope.
Notation "'(' C '×-)'" := (BinaryProductBiFunctor ◯ (Const C × Id)) : functor_scope.