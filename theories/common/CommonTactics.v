Require Export Program Axioms sflib.
Require Export Permutation Orders String HexString ZArith List.
Export ListNotations.

From stdpp Require Export ssreflect.

Create HintDb normalize discriminated.
Create HintDb coqcat discriminated.

Ltac normalize := autorewrite with normalize.
Tactic Notation "normalize" "in" hyp(H) := autorewrite with normalize in H.
Tactic Notation "normalize" "in" "*|-" := repeat_on_hyps (fun H => normalize in H).
Tactic Notation "normalize" "in" "*" := autorewrite with normalize in *.

Ltac cat := eauto with coqcat.

Ltac cat_simpl :=
  ii; ss; setoid_subst;
  try solve_proper;
  normalize in *;
  try by cat.

Global Obligation Tactic := program_simpl; cat_simpl.