Require Import Category.Lib.Base.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Axiom ExcludedMiddle : Type.
Existing Class ExcludedMiddle.

Axiom LEM : ∀ `{ExcludedMiddle} (P : Type), P ∨ ¬ P.

Tactic Notation "classic" uconstr(P) := destruct (LEM P).
Tactic Notation "classic" uconstr(P) "as" ident(H) := destruct (LEM P) as [H|H].