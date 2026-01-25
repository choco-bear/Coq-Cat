Require Import Coq.Vectors.Fin.
Require Import Coq.Lists.List.
Require Import Category.Lib.
Require Import Category.Algebra.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Facts.Group.Automorphism.
Require Import Category.Facts.Group.Cyclic.

Generalizable All Variables.

Import ListNotations.

(** The symmetric group S_n is the group of automorphisms on an n-element set. *)
Program Definition SymmetricGroup (n : nat) : Group :=
  Aut[Sets] (@Fin_Setoid n).

Notation "'S[' n ']'" := (SymmetricGroup n%nat)
  (at level 0, format "S[ n ]") : group_type_scope.

(* TODO : Define the sign of permutation. *)
Section Sign.
End Sign.