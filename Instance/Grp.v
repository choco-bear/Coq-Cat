Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Groupoid.

Generalizable All Variables.

(** The category [Grp] is a category, whose objects are groups, and whose morphisms
  * are group-homomorphisms. *)
Program Definition Grp : Category :=
  {|  obj := Group
    ; hom := GroupHomomorphism
    ; homset := @group_hom_setoid

    ; id := grp_id_map

    ; compose := @grp_hom_comp
    ; compose_respects := @grp_hom_comp_respects
    
    ; id_left := @grp_id_map_left
    ; id_right := @grp_id_map_right
  |}.