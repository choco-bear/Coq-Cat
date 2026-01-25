Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Instance.Cat.
From Category.Construction Require Import Product Opposite.

Generalizable All Variables.

(** This file defines important functors related to the category of categories. *)

(** Opposite functor is the functor mapping each category to its opposite category. *)
Section OppositeFunctor.
  Program Definition OppositeFunctor : Cat ⟶ Cat :=
    {|  fobj := λ C : Cat, C^op : Cat
      ; fmap := 
          λ (C D : Cat) (T : C ~{Cat}~> D),
            {|  fobj := λ x : C^op, T x : D^op
              ; fmap := λ (x y : C^op) (f : x ~{C^op}~> y), fmap[T] f
            |}
    |}.
  Next Obligation. proper; construct;
    first [now natural_transform; ss; try apply component, X; cat; normalize|cat_simpl].
  Qed.
  Next Obligation. by functor_equiv_solver. Qed.
  Next Obligation. by functor_equiv_solver. Qed.
End OppositeFunctor.
Notation "'(-)^op'" := OppositeFunctor : functor_scope.


(** Fun functor is the bifunctor mapping each pair [(A,B)] of categories to the category
  * [Fun[A,B]].
  *)
Section FunBiFunctor.
  Definition FunBiFunctor_fobj := λ`(A,B) : obj[Cat^op × Cat], Fun[A,B] : Cat.
  
  Definition FunBiFunctor_fmap {x y : obj[Cat^op × Cat]} (f : x ~> y)
    : FunBiFunctor_fobj x ~> FunBiFunctor_fobj y.
  Proof.
    do 2 cat. srapply FromAFunctor; try exact (λ X, H ◯ X ◯ f).
    construct; [exact (_ ▪ f0 ▪ _)|proper; rewrites|..]; by ss.
  Defined.
  #[export] Arguments FunBiFunctor_fmap : simpl never.

  Local Obligation Tactic := idtac.
  Program Definition FunBiFunctor : Cat^op × Cat ⟶ Cat :=
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
End FunBiFunctor.
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
    do 2 cat. srapply FromAFunctor; try exact (λ`(a,b), (f a, H b)).
    construct; first [by cat|proper; rewrites]; done.
  Defined.
  #[export] Arguments BinaryProductBiFunctor_fmap : simpl never.

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
End BinaryProductBiFunctor.
Notation "'(-×-)'" := BinaryProductBiFunctor : functor_scope.
Notation "'(-×' C ')'" := (BinaryProductBiFunctor ◯ (Id × Const C)) : functor_scope.
Notation "'(' C '×-)'" := (BinaryProductBiFunctor ◯ (Const C × Id)) : functor_scope.