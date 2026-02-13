Require Export Program Axioms sflib.
Require Export Permutation Orders String HexString ZArith List.
Export ListNotations.
Require Export Category CategoryFacts.

From stdpp Require Export ssreflect.

Global Obligation Tactic := program_simpl; ii; ss.