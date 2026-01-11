Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Universe Polymorphism.

(** A finite object is a setoid object equipped with a finiteness proof. *)
Record FiniteObject : Type :=
  { carrier :> SetoidObject
  ; is_finite :> Finite (is_setoid carrier)
  }.
#[export] Existing Instance is_finite.

Definition of_finite `{SET : Setoid A} (FIN : Finite SET) : FiniteObject :=
  {|  carrier := of_setoid SET
    ; is_finite := FIN
  |}.
#[export] Coercion of_finite : Finite >-> FiniteObject.

(** The category of finite types *)
Program Definition Fin : Category :=
  {|  obj := FiniteObject
    ; hom := @SetoidMorphism
    ; homset := @SetoidMorphism_Setoid

    ; id := @SetoidMorphism_id
    ; compose := @SetoidMorphism_compose
    ; compose_respects := @SetoidMorphism_compose_respects
  |}.