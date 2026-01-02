Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Axiom ExcludedMiddle : Type.
#[export] Existing Class ExcludedMiddle.

Axiom LEM : ∀ `{ExcludedMiddle} (P : Type), P ∨ ¬ P.
#[export] Hint Resolve LEM : core.

Tactic Notation "classic" uconstr(P) := destruct (LEM P).
Tactic Notation "classic" uconstr(P) "as" ident(H) := destruct (LEM P) as [H|H].
Tactic Notation "classic" :=
  repeat match goal with
  | |- context[LEM ?x] => destruct (LEM x); cat
  end.


Global Instance ExcludedMiddle_Decidable
  `{ExcludedMiddle} `(SET : Setoid A) : Decidable SET.
Proof. construct; auto. Qed.