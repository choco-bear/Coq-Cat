Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

Program Definition AutomorphismGroup {C : Category} (x : C) : Group :=
  {|  grp_carrier := x ≅ x
    ; grp_setoid := iso_setoid
    ; grp_op := {| op := iso_compose |}

    ; grp_id := iso_id

    ; grp_inv := iso_sym
  |}.

Notation "'Aut'" := (AutomorphismGroup) : group_scope.
Notation "'Aut[' C ']'" :=
  (@AutomorphismGroup C) (only parsing) : group_scope.


Require Import Category.Instance.Sets.
Program Definition SymmetricGroup (n : nat) : Group :=
  Aut[Sets] {| is_setoid := @Fin_Setoid n |}.