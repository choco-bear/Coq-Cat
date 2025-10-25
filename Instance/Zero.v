Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** The zero category, with no objects and no morphisms. Also called the empty
  * category.
  *)
#[local] Obligation Tactic :=
  intros; try match goal with H : Empty_set |- _ => destruct H end.
Program Definition _0 : Category := 
  {| obj := Empty_set
   ; hom := fun _ _ => Empty_set
   ; homset := Morphism_equality
  |}.

Notation "0" := _0 : category_scope.

(** The unique functor from the zero category to any other category. *)
#[export]
Program Instance From_0 (C : Category) : 0 ⟶ C.
Next Obligation. destruct X. Defined.
Next Obligation. destruct x. Defined.
Next Obligation. destruct x. Qed.
Next Obligation. destruct x. Qed.
