Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.Setoid.
Require Import Category.Instance.Cat.
From Category.Construction Require Import Product Opposite.

Generalizable All Variables.

(** This file defines important functors related to the category of categories. *)

(** Opposite functor is the functor mapping each category to its opposite category. *)
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

Notation "'(-)^op'" := OppositeFunctor : functor_scope.


(** Fun functor is the bifunctor mapping each pair [(A,B)] of categories to the category
  * [Fun[A,B]].
  *)
Program Definition FunBiFunctor : Cat^op × Cat ⟶ Cat :=
  {|  fobj := λ`(A,B) : obj[Cat^op × Cat], Fun[A,B] : Cat
    ; fmap :=
        λ`(A,B) : obj[Cat^op × Cat],
        λ`(A',B') : obj[Cat^op × Cat],
        λ`(F,G) : (A,B) ~{Cat^op × Cat}~> (A',B'),
          {| fobj := λ T : Fun[A,B], G ◯ T ◯ F : Fun[A',B'] |}
  |}.
Next Obligation.
  natural_transform; ss.
  - now apply fmap, component.
  - cat. by rewrite naturality.
Defined.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
(* Next Obligation.
  (** TODO : If we have any lemmas constructing isomorphisms by the fact that two functors are
    *        equivalent, this proof may be shorter and the compilation time would be reduced.
    *)
  proper; ss. destruct a, b. unshelve econs; ss.
  - isomorphism; ss.
    + natural_transform; ss.
      * left (x1 _). do 2 apply fmap. apply x0.
      * rewrite !e0, !e. ss. normalize. repeat comp_right.
        now rewrite <-!fmap_comp; normalize.
    + natural_transform; ss.
      * left ((x0 _)⁻¹). do 2 apply fmap. apply x1.
      * rewrite !e0, !e. ss. normalize. repeat comp_left.
        now rewrite <-!fmap_comp; normalize.
    + ss. rewrite !e. normalize. now rewrite <-!fmap_comp; normalize.
    + ss. rewrite !e. normalize.
      now rewrite <-(comp_assoc (x0 (x2 (x x3)))⁻¹), <-!fmap_comp; normalize.
  - ss. rewrite !e. normalize. comp_left. comp_right.
    rewrite <-!fmap_comp. apply fmap_respects.
    pose (naturality f (x1 x3)). rewrite <-comp_assoc, e1, comp_assoc.
    by assert (fmap[y0] (x1 x3)⁻¹ ∘ fmap[y0] (x1 x3) ≡ id) as ->
      by by rewrite <-fmap_comp.
Qed. *)
(* Next Obligation. by construct; [isomorphism; ss; by first [natural_transform; ss|idtac]|]. Qed. *)
(* Next Obligation. by construct; [isomorphism; ss; by first [natural_transform; ss|idtac]|]. Qed. *)

Notation "'Fun[-,-]'" := FunBiFunctor : functor_scope.
Notation "'Fun[' C ',-]'" :=
  (FunBiFunctor ◯ (Const (C%category : Cat^op) × Id)) : functor_scope.
Notation "'Fun[-,' D ']'" :=
  (FunBiFunctor ◯ (Id × Const D%category)) : functor_scope.


(** Prod functor is the bifunctor mapping each pair [(A,B)] of categories to the category
  * [A × B].
  *)
Program Definition BinaryProductBiFunctor : Cat × Cat ⟶ Cat :=
  {|  fobj := λ`(A,B) : obj[Cat × Cat], (A × B)%category : Cat
    ; fmap :=
        λ`(A,B) : obj[Cat × Cat],
        λ`(A',B') : obj[Cat × Cat],
        λ`(F,G) : (A,B) ~{Cat × Cat}~> (A',B'),
          {|  fobj := λ`(a,b) : obj[A × B], (F a, G b) : obj[A' × B']
            ; fmap :=
                λ`(a1,b1) : obj[A × B],
                λ`(a2,b2) : obj[A × B],
                λ`(f,g) : (a1,b1) ~{A × B}~> (a2,b2),
                  (fmap[F] f, fmap[G] g) : (F a1, G b1) ~{A' × B'}~> (F a2, G b2)
          |}
  |}.
Next Obligation. proper; ss; first [by isomorphism; cat; ss; normalize|ss]. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Notation "'(-×-)'" := BinaryProductBiFunctor : functor_scope.
Notation "'(-×' C ')'" := (BinaryProductBiFunctor ◯ (Id × Const C)) : functor_scope.
Notation "'(' C '×-)'" := (BinaryProductBiFunctor ◯ (Const C × Id)) : functor_scope.