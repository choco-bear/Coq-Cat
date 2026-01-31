Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.
Require Import Category.Construction.Fun.
Require Import Category.Construction.Product.

Generalizable All Variables.

Section Curry.
  Context {A : Category} {B : Category} {C : Category}.

  Definition curry_fobj (T : A × B ⟶ C) (a : A) : Fun[B,C].
  Proof.
    srapply FromAFunctor; try exact (λ b, T (a,b)).
    construct; unshelve cat; try exact (id,f); cat.
    now proper; rewrites.
  Defined.

  Definition fmap_curry_fobj (T : A × B ⟶ C) (a : A) `(f : x ~{B}~> y)
    : fmap[curry_fobj T a] f = fmap[T] ((id, f) : (a, x) ~{A × B}~> (a, y)) := eq_refl.

  Definition curry_fmap (T : A × B ⟶ C) {x y : A} (f : x ~> y)
    : curry_fobj T x ~> curry_fobj T y.
  Proof. cat; natural_transform; ss; try refine (fmap[T] _); cat. by rewrite ?fmap_curry_fobj. Defined.
  #[export] Arguments curry_fmap : simpl never.

  Program Definition curry (T : A × B ⟶ C) : A ⟶ Fun[B,C] :=
    {|  fobj := curry_fobj T
      ; fmap := @curry_fmap T 
    |}.

  Definition fmap_curry (T : A × B ⟶ C) `(f : x ~{A}~> y) (c : B)
    : fmap[curry T] f c = curry_fmap T f c := eq_refl.
End Curry.
#[export] Hint Rewrite @fmap_curry_fobj @fmap_curry : categories normalize.

Section Uncurry.
  Context {A : Category} {B : Category} {C : Category}.

  Definition uncurry_fobj (T : A ⟶ Fun[B,C]) (x : obj[A × B])
    : C := match x with (a,b) => T a b end.

  Definition uncurry_fmap (T : A ⟶ Fun[B,C]) {x y : obj[A × B]} (f : x ~> y)
    : uncurry_fobj T x ~> uncurry_fobj T y.
  Proof. do 2 cat. exact (fmap[T y] f0 ∘ fmap[T] f _). Defined.

  Program Definition uncurry (T : A ⟶ Fun[B,C]) : (A × B ⟶ C) :=
    {|  fobj := uncurry_fobj T
      ; fmap := @uncurry_fmap T
    |}.
  Next Obligation.
    proper; ss; srapply compose_respects; try now rewrites.
    now sufficient (fmap[T] x ≡ fmap[T] y); rewrites.
  Qed.
  Next Obligation. now sufficient (fmap[T] id[o] ≡ id); normalize. Qed.
  Next Obligation.
    normalize. cat. comp_left.
    now sufficient (fmap[T] (h1 ∘ h) ≡ fmap[T] h1 ∘ fmap[T] h); normalize.
  Qed.

  Definition fmap_uncurry (T : A ⟶ Fun[B,C]) `(f1 : x1 ~{A}~> y1) `(f2 : x2 ~{B}~> y2)
    : fmap[uncurry T] ((f1, f2) : (x1, x2) ~{A × B}~> (y1, y2)) = fmap[T y1] f2 ∘ fmap[T] f1 x2 := eq_refl.
End Uncurry.
#[export] Hint Rewrite @fmap_uncurry : categories normalize.