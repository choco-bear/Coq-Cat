Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.
Set Universe Polymorphism.

Module Defs.
  (** A setoid object is a type equipped with an equivalence relation. *)
  Record SetoidObject : Type :=
    { carrier :> Type
    ; is_setoid :> Setoid carrier
    }.
  #[export] Existing Instance is_setoid.

  (** A setoid morphism is a function between setoid objects that respects the
    * equivalence relations on the source and target setoids.
    *)
  Record SetoidMorphism {x : SetoidObject} {y : SetoidObject} :=
    { morphism : x → y
    ; proper_morphism : Proper (equiv ==> equiv) morphism
    }.
  Arguments proper_morphism {_ _ _} _ _ /.
  #[export] Existing Instance proper_morphism.

  Arguments SetoidMorphism _ _ : clear implicits.
  Arguments morphism {_ _ _} _.
  Coercion morphism : SetoidMorphism >-> Funclass.

  (** Equivalence relation over the setoid morphisms is defined as functional
    * extensionality. *)
  Definition SetoidMorphism_equiv {x y : SetoidObject}
    : crelation (SetoidMorphism x y) :=
      λ f g, ∀ a, @equiv _ y (f a) (g a).

  Arguments SetoidMorphism_equiv {x y} _ _ /.

  (** Setoid structure on the setoid morphisms. *)
  #[export]
  Program Instance SetoidMorphism_Setoid {x y : SetoidObject}
    : Setoid (SetoidMorphism x y) :=
      {| equiv := SetoidMorphism_equiv |}.
  Next Obligation. equivalence. now transitivity (y0 a). Qed.
  
  #[export]
  Instance morphism_is_proper {x y : SetoidObject}
    : Proper (equiv ==> equiv ==> equiv) (@morphism x y).
  Proof. proper; now rewrites. Qed.

  (** Identity morphism *)
  Definition SetoidMorphism_id {x : SetoidObject}
    : SetoidMorphism x x := {| morphism := Datatypes.id |}.
  #[export] Hint Unfold SetoidMorphism_id : core.

  (** Setoid morphism composition *)
  Program Definition SetoidMorphism_compose
    {x y z : SetoidObject} (f : SetoidMorphism y z) (g : SetoidMorphism x y)
    : SetoidMorphism x z := {| morphism := λ a, f (g a) |}.
  Next Obligation. proper. now do 2 apply proper_morphism. Qed.
  #[export] Hint Unfold SetoidMorphism_compose : core.

  #[export]
  Instance SetoidMorphism_compose_respects
    {x y z : SetoidObject}
    : Proper (equiv ==> equiv ==> equiv)
      (@SetoidMorphism_compose x y z).
  Proof. proper. now rewrites. Qed.

  (** Function between SetoidObjects is also a SetoidObject *)
  Definition SetoidObject_function
    (X : SetoidObject) (Y : SetoidObject) : SetoidObject :=
      {| carrier := SetoidMorphism X Y
       ; is_setoid := SetoidMorphism_Setoid |}.

  (** Product of SetoidObjects is also a SetoidObject *)
  Definition SetoidObject_prod
    (X : SetoidObject) (Y : SetoidObject) : SetoidObject :=
      {| carrier := X * Y |}.

  (** Sum of SetoidObjects is also a SetoidObject *)
  Definition SetoidObject_sum
    (X : SetoidObject) (Y : SetoidObject) : SetoidObject :=
      {| carrier := X + Y |}.
End Defs.
Export Defs.

(** The category of setoids and setoid morphisms. *)
Program Definition Sets : Category :=
  {| obj := SetoidObject : Type
   ; hom := λ x y, SetoidMorphism x y : Type
   ; homset := @SetoidMorphism_Setoid
   ; id := @SetoidMorphism_id
   ; compose := @SetoidMorphism_compose
   ; compose_respects := @SetoidMorphism_compose_respects
  |}.

(* [fequal] for setoid morphisms. *)
Ltac setoid_fequal := apply morphism_is_proper; [|reflexivity].