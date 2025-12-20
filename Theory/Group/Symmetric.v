Require Import Category.Lib.
Require Import Category.Theory.Group.Automorphism.
Require Import Category.Instance.Sets.

(** The symmetric group S_n is the group of automorphisms on an n-element set. *)
Program Definition SymmetricGroup (n : nat) : Group :=
  Aut[Sets] (of_setoid (@Fin_Setoid n)).

(* TODO : Define the sign of permutation. *)