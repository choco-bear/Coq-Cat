Require Export Program Axioms sflib.
Require Export Permutation Orders String HexString ZArith List.
Export ListNotations.

From stdpp Require Export ssreflect.

Create HintDb normalize discriminated.
Create HintDb coqcat discriminated.

Global Hint Rewrite @compose_id_right @compose_id_left.

Ltac common_normalize := autorewrite with normalize.
Tactic Notation "common_normalize" "in" hyp(H) := autorewrite with normalize in H.
Tactic Notation "common_normalize" "in" "*" "|-" := repeat_on_hyps (fun H => common_normalize in H).
Tactic Notation "common_normalize" "in" "*" := autorewrite with normalize in *.

Ltac cat := eauto with coqcat.

Ltac common_simpl :=
  ii; ss; subst;
  try apply _;
  try solve_proper;
  tryif (
    solve [ common_normalize in *; try by cat]
  ) then idtac else (
    common_normalize; try by cat
  ).

Global Obligation Tactic := program_simpl; common_simpl.