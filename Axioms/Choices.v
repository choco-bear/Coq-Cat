Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Axiom Choice : Type.
#[export] Existing Class Choice.

Axiom AC_fun : ∀ `{Choice} `(R : A → B → Type),
  (∀ x, ∃ y, R x y) → ∃ f, ∀ x, R x (f x).
Axiom AC_fun_dep : ∀ `{Choice} `(R : ∀ x : A, B x → Type),
  (∀ x, ∃ y, R x y) → ∃ f, ∀ x, R x (f x).
Axiom DC_fun : ∀ `{Choice} `(R : crelation A),
  (∀ x, ∃ y, R x y) → ∀ x, ∃ f, f O = x ∧ ∀ n, R (f n) (f (S n)).
Axiom AC_fun_repr : ∀ `{Choice} `(@Equivalence A R),
  ∃ f, ∀ x, R x (f x) ∧ ∀ x', R x x' → f x = f x'.
Axiom AC_fun_setoid : ∀ `{Choice} `(@Equivalence A R) `(T : A → B → Type),
  Proper (R ==> eq ==> iffT) T → (∀ x, ∃ y, T x y)
→ ∃ f, ∀ x, T x (f x) ∧ ∀ x', R x x' → f x = f x'.